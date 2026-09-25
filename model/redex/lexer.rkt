#lang racket

(require "diagnostic.rkt")

(provide (struct-out stok) lex lex/string)

;; spec §4.2。kind は int str ident kw punct nl eof のいずれかである。
(struct stok (kind value span) #:transparent)

(define keywords '(const let mut fn type true false trait impl for derive))
(define puncts (hash 123 '|{| 125 '|}| 40 '|(| 41 '|)|
                     44 '|,| 58 '|:| 61 '|=| 46 '|.|
                     124 '\| 38 '&))

(define (span id a b) `(#:span ,id ,a ,b))

(define (ident-start? b)
  (or (and (>= b 65) (<= b 90))
      (and (>= b 97) (<= b 122))
      (= b 95)))

(define (ident-rest? b)
  (or (ident-start? b) (digit? b)))

(define (digit? b) (and (>= b 48) (<= b 57)))

(define (space? b) (or (= b 32) (= b 9)))

(define (lex/string id str)
  (lex id (string->bytes/utf-8 str)))

(define (lex id bs)
  (define n (bytes-length bs))
  ;; spec §4.4。不正 byte の検査は走査より前に 1 度だけ行い、入力の全体を
  ;; 覆う。コメントの中も文字列リテラルの中も同じに扱う。この検査は他の
  ;; どの字句の誤りよりも優先する。走査順の最初の 1 件という規則は、この
  ;; 検査を通った入力の中でだけ効く。
  (define bad (first-invalid-byte bs n))
  (cond
    [bad (sur 'surface-invalid-byte (span id bad (add1 bad)))]
    [else (scan id bs n)]))

(define (sur key s)
  (diagnostic-of 'surface key #:primary-span s))

(define (scan id bs n)
  ;; 走査は byte 添字で進める。char へ変換しないのは、span が byte 位置を
  ;; 指すためである。
  (let loop ([i 0] [acc '()])
    (cond
      [(>= i n) (reverse (cons (stok 'eof 'eof (span id n n)) acc))]
      [(space? (bytes-ref bs i)) (loop (add1 i) acc)]
      [(comment-start? bs n i) (loop (skip-comment bs n i) acc)]
      [(= (bytes-ref bs i) 10)
       (define j (skip-nl-run bs n i))
       (loop j (cons (stok 'nl 'nl (span id i j)) acc))]
      [(digit? (bytes-ref bs i))
       (define j (scan-while bs n i digit?))
       (define v (string->number (bytes->string/utf-8 (subbytes bs i j))))
       (loop j (cons (stok 'int v (span id i j)) acc))]
      [(ident-start? (bytes-ref bs i))
       (define j (scan-while bs n i ident-rest?))
       (define sym (string->symbol (bytes->string/utf-8 (subbytes bs i j))))
       (define k (if (memq sym keywords) 'kw 'ident))
       (loop j (cons (stok k sym (span id i j)) acc))]
      ;; SUR-011。- は単独の記号ではなく、直後の > と合わせて 1 token にする。
      [(and (= (bytes-ref bs i) 45)
            (< (add1 i) n)
            (= (bytes-ref bs (add1 i)) 62))
       (loop (+ i 2) (cons (stok 'punct '-> (span id i (+ i 2))) acc))]
      [(hash-ref puncts (bytes-ref bs i) #f)
       => (lambda (p)
            (loop (add1 i) (cons (stok 'punct p (span id i (add1 i))) acc)))]
      [(= (bytes-ref bs i) 34)
       (define result (scan-string id bs n i))
       (if (diagnostic? result)
           result
           (let ([j (car result)] [str (cdr result)])
             (loop j (cons (stok 'str str (span id i j)) acc))))]
      [else
       (define j (code-point-end bs n i))
       (sur 'surface-unknown-character (span id i j))])))

(define (scan-while bs n i pred)
  (let go ([j i])
    (if (and (< j n) (pred (bytes-ref bs j))) (go (add1 j)) j)))

(define (comment-start? bs n i)
  (and (< (add1 i) n)
       (= (bytes-ref bs i) 47)
       (= (bytes-ref bs (add1 i)) 47)))

;; 行コメントは改行の手前で止める。改行そのものは nl として残す。
(define (skip-comment bs n i)
  (let go ([j i])
    (if (and (< j n) (not (= (bytes-ref bs j) 10))) (go (add1 j)) j)))

;; spec §4.2。連続する改行は 1 つの nl へ畳む。run には改行の間の空白と
;; 行コメントも含める。span は run 全体を覆う。
(define (skip-nl-run bs n i)
  (let go ([j i] [last (add1 i)])
    (cond
      [(>= j n) last]
      [(= (bytes-ref bs j) 10) (go (add1 j) (add1 j))]
      [(space? (bytes-ref bs j)) (go (add1 j) last)]
      [(comment-start? bs n j) (go (skip-comment bs n j) last)]
      [else last])))

;; spec §4.5。文字列の中では、許さないエスケープが閉じない末尾より先に返る。
;; 逆斜線の次が入力の末尾か改行の場合は E-SUR-003 である。
(define (scan-string id bs n i)
  (let go ([j (add1 i)] [out '()])
    (cond
      [(>= j n) (sur 'surface-unterminated-string (span id i n))]
      [(= (bytes-ref bs j) 10)
       (sur 'surface-unterminated-string (span id i j))]
      [(= (bytes-ref bs j) 34)
       (cons (add1 j)
             (bytes->string/utf-8 (list->bytes (reverse out))))]
      [(= (bytes-ref bs j) 92)
       (define k (add1 j))
       (cond
         [(or (>= k n) (= (bytes-ref bs k) 10))
          (sur 'surface-unterminated-string
               (span id i (if (>= k n) n k)))]
         [else
          (define c (case (bytes-ref bs k)
                      [(34) 34] [(92) 92] [(110) 10] [(116) 9] [else #f]))
          (if c
              (go (+ j 2) (cons c out))
              (sur 'surface-invalid-escape
                   (span id j (code-point-end bs n k))))])]
      [else (go (add1 j) (cons (bytes-ref bs j) out))])))

;; UTF-8 として解釈できない最初の byte の位置を返す。無ければ #f である。
(define (first-invalid-byte bs n)
  (let go ([i 0])
    (cond
      [(>= i n) #f]
      [else
       (define len (utf8-length (bytes-ref bs i)))
       (cond
         [(not len) i]
         [(> (+ i len) n) i]
         [(not (continuations-ok? bs i len)) i]
         [(not (utf8-canonical? bs i len)) i]
         [else (go (+ i len))])])))

(define (utf8-length b)
  (cond
    [(< b #x80) 1]
    [(< b #xC2) #f]
    [(< b #xE0) 2]
    [(< b #xF0) 3]
    [(< b #xF5) 4]
    [else #f]))

(define (continuations-ok? bs i len)
  (for/and ([k (in-range 1 len)])
    (= (bitwise-and (bytes-ref bs (+ i k)) #xC0) #x80)))

;; 過長表現と surrogate と上限超えを弾く。
(define (utf8-canonical? bs i len)
  (define b0 (bytes-ref bs i))
  (define b1 (and (> len 1) (bytes-ref bs (add1 i))))
  (cond
    [(= len 3) (not (or (and (= b0 #xE0) (< b1 #xA0))
                        (and (= b0 #xED) (>= b1 #xA0))))]
    [(= len 4) (not (or (and (= b0 #xF0) (< b1 #x90))
                        (and (= b0 #xF4) (>= b1 #x90))))]
    [else #t]))

;; 位置 i から始まる code point の末尾の次の位置を返す。全体検査を通った
;; 入力にだけ使うので、len が #f になることは無い。
(define (code-point-end bs n i)
  (min n (+ i (or (utf8-length (bytes-ref bs i)) 1))))
