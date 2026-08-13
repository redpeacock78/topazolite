#lang racket

(provide format-unfixed
         unfixed->jsexpr
         source-id->uri
         span->jsexpr)

(require json
         racket/match)

;; spec §11: 形を固定しない 4 欄（expected、found、effect-context、
;; proof-context）の整形。3 つの renderer がこの 1 つの関数を共有する。
;; ~a ではなく ~s を使うのは、文字列と記号を見分けられるようにするためである。
;; capability-diagnostic の reason は文字列で found へ入るため、~a にすると
;; 型項の記号と区別が付かない。
(define (format-unfixed v)
  (format "~s" v))

;; #f は「値が無い」を表す。#f そのものを表示すると、found が偽値であった診断と
;; 区別が付かない。
(define (unfixed->jsexpr v)
  (if v (format-unfixed v) (json-null)))

(define (synthetic-sid? sid)
  (eq? sid '#:synthetic))

;; #:synthetic は keyword なので symbol->string を使えない。
;; 綴りは JSON の span object と LSP の data で同じにする。
(define (sid-spelling sid)
  (if (synthetic-sid? sid) "#:synthetic" (symbol->string sid)))

;; spec §10 の span object。JSON と LSP の data が同じ形を使う。
(define (span->jsexpr span)
  (match-define (list '#:span sid start end) span)
  (hasheq 'sourceId (sid-spelling sid)
          'startByte start
          'endByte end
          'synthetic (synthetic-sid? sid)))

;; spec §9: sourceId から URI への変換。
;; (format "topazolite:~a" sid) の形は採らない。#:synthetic の # が fragment の
;; 区切りになり、URI から sourceId を復元できない。
;; RFC 3986 の unreserved 以外の byte をすべて %XX の 2 桁大文字 16 進へ写す。
(define unreserved-bytes
  (list->seteqv
   (bytes->list
    #"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-._~")))

(define (percent-encode-byte b)
  (string-upcase
   (if (< b 16)
       (format "%0~a" (number->string b 16))
       (format "%~a" (number->string b 16)))))

;; 変換を 1 つの関数へ閉じる。LSP renderer の 2 箇所で組むと、片方だけが
;; encoding を欠いた形になる。
(define (source-id->uri sid)
  (string-append
   "topazolite:"
   (apply string-append
          (for/list ([b (in-bytes (string->bytes/utf-8 (sid-spelling sid)))])
            (if (set-member? unreserved-bytes b)
                (string (integer->char b))
                (percent-encode-byte b))))))
