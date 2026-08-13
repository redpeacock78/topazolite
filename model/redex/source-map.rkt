#lang racket

(provide make-source-map
         source-map?
         source-map-source
         (struct-out location)
         span->location
         utf-16-length)

(require racket/match
         "span-core.rkt")

;; source-map は sourceId の記号から source 文字列への表である（spec §6）。
;; 構造体にするのは、検査を通らない表を作れなくするためである。素の hash を
;; 受け取る形にすると、make-source-map を経ない表が span->location へ入る
;; 経路が残る。
(struct source-map (table) #:transparent)

;; 誤りの報告順を実行ごとに変えないため、key を綴りで並べてから検査する。
;; hash の走査順は指定されていないので、複数の行が不正な表では報告される行が
;; 揺れる。
(define (sorted-keys table)
  (sort (hash-keys table) string<? #:key (lambda (k) (format "~s" k))))

;; 表の検査は spec §6 の 4 つを、それぞれ別の走査として置く。1 つの走査へ畳むと、
;; key の種類の誤りと value の種類の誤りが同じ表に混ざったとき、どちらが先に
;; 出るかが key の綴りで決まってしまう。
(define (make-source-map table)
  (unless (hash? table)
    (error 'make-source-map "hash でなければならない: ~s" table))
  (define keys (sorted-keys table))
  (for ([key (in-list keys)])
    (unless (symbol? key)
      (error 'make-source-map "key は記号でなければならない: ~s" key)))
  (for ([key (in-list keys)])
    (define value (hash-ref table key))
    (unless (string? value)
      (error 'make-source-map "value は文字列でなければならない: ~s ~s" key value)))
  (for ([key (in-list keys)])
    (when (regexp-match? #rx"\r" (hash-ref table key))
      (error 'make-source-map "value は CR を含んではならない: ~s" key)))
  (for ([key (in-list keys)])
    (when (regexp-match? #rx"[\n\r]" (symbol->string key))
      (error 'make-source-map "key の記号名は改行を含んではならない: ~s" key)))
  ;; 受け取った hash が可変なら構築の後で書き換えられる。検査した内容を
  ;; 凍らせるため、不変の hasheq へ写す。
  (source-map
   (for/hasheq ([key (in-list keys)])
     (values key (hash-ref table key)))))

(define (source-map-source sm sid)
  (hash-ref (source-map-table sm) sid
            (lambda ()
              (error 'span->location
                     "source-map に無い sourceId である: ~s" sid))))

;; 0 起点の行と、0 起点の UTF-16 code unit 単位の列を持つ（spec §6）。
;; LSP の Position に合わせた単位であり、1 起点で表示する renderer が変換を
;; 1 箇所で行う。
(struct location
  (source-id synthetic? start-line start-character end-line end-character)
  #:transparent)

;; UTF-16 code unit 数。基本多言語面の外の文字は 2 を数える。
;; Racket の文字列は Unicode scalar の列なので、byte 単位でも文字単位でもない
;; 第 3 の単位を明示的に数える必要がある。
(define (utf-16-length s)
  (for/sum ([ch (in-string s)])
    (if (>= (char->integer ch) #x10000) 2 1)))

;; UTF-8 の後続 byte は上位 2 bit が 10 の byte である。
(define (continuation-byte? b)
  (= (bitwise-and b #b11000000) #b10000000))

;; 2 つの offset を別々に検査し、error の文へどちらが不正かを含める。
;; byte 長と等しい offset は許す。source の末尾を指す空 span は正当な位置であり、
;; 末尾に挿入を提案する診断が使う。
(define (check-offset! name offset bs)
  (define len (bytes-length bs))
  (when (> offset len)
    (error 'span->location
           "~a が source の byte 長を超えている: ~a > ~a" name offset len))
  (when (and (< offset len) (continuation-byte? (bytes-ref bs offset)))
    (error 'span->location "~a が UTF-8 の文字境界にない: ~a" name offset)))

;; 境界の検査を済ませた offset なので、前半の byte 列は必ず文字列へ戻せる。
;; 検査より先に bytes->string/utf-8 を通す形にはしない。文字の途中で切った
;; byte 列は例外になるか置換文字を混ぜて通り、どちらも位置の誤りが位置の誤りと
;; して現れない。
(define (offset->line+character bs offset)
  (for/fold ([line 0] [character 0])
            ([ch (in-string (bytes->string/utf-8 (subbytes bs 0 offset)))])
    (cond
      [(char=? ch #\newline) (values (add1 line) 0)]
      [(>= (char->integer ch) #x10000) (values line (+ character 2))]
      [else (values line (add1 character))])))

;; spec §6 の 3 段。段の順序を入れ替えてはならない。
;; 第 1 段は span-ok?（形と startByte <= endByte）、第 2 段は synthetic 分岐、
;; 第 3 段は source-map lookup と byte 長・文字境界の検査である。
(define (span->location sm span)
  (unless (span-ok? span)
    (error 'span->location "span-ok? を満たさない span である: ~s" span))
  (match-define (list '#:span sid start end) span)
  (cond
    ;; synthetic は source を持たないので表を引かない。
    [(eq? sid '#:synthetic) (location sid #t 0 0 0 0)]
    [else
     (define bs (string->bytes/utf-8 (source-map-source sm sid)))
     (check-offset! 'startByte start bs)
     (check-offset! 'endByte end bs)
     (define-values (start-line start-character) (offset->line+character bs start))
     (define-values (end-line end-character) (offset->line+character bs end))
     (location sid #f start-line start-character end-line end-character)]))
