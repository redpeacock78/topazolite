#lang racket

(require "diagnostic.rkt")

(provide (struct-out stok) lex lex/string)

;; spec §4.2。kind は int str ident kw punct nl eof のいずれかである。
(struct stok (kind value span) #:transparent)

(define keywords '(const let mut fn type true false))
(define puncts (hash 123 '|{| 125 '|}| 40 '|(| 41 '|)|
                     44 '|,| 58 '|:| 61 '|=| 46 '|.|))

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
      [(hash-ref puncts (bytes-ref bs i) #f)
       => (lambda (p)
            (loop (add1 i) (cons (stok 'punct p (span id i (add1 i))) acc)))]
      [(= (bytes-ref bs i) 34)
       (define-values (j str) (scan-string bs n i))
       (loop j (cons (stok 'str str (span id i j)) acc))]
      [else (error 'lex "Task 4 で拒否経路を足すまでの穴である: ~s" i)])))

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

;; この段では閉じない文字列と許さないエスケープを扱わない。Task 4 で足す。
(define (scan-string bs n i)
  (let go ([j (add1 i)] [out '()])
    (cond
      [(>= j n) (error 'lex "Task 4 で E-SUR-003 を足すまでの穴である")]
      [(= (bytes-ref bs j) 34)
       (values (add1 j)
               (bytes->string/utf-8 (list->bytes (reverse out))))]
      [(= (bytes-ref bs j) 92)
       (define e (and (< (add1 j) n) (bytes-ref bs (add1 j))))
       (define c (case e [(34) 34] [(92) 92] [(110) 10] [(116) 9] [else #f]))
       (if c
           (go (+ j 2) (cons c out))
           (error 'lex "Task 4 で E-SUR-004 を足すまでの穴である"))]
      [else (go (add1 j) (cons (bytes-ref bs j) out))])))
