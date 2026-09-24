#lang racket

(require "lexer.rkt"
         "parser.rkt"
         "surface-lower.rkt"
         "elaborate.rkt"
         "diagnostic.rkt"
         (only-in "origins.rkt" current-trait-env))

(provide compile-source compile-source/string (struct-out compiled))

;; spec §5。成功の成果物である。欄は elab の返り値の 4 要素と同じ順で並べる。
;; core は span を持つ Typed Core であり、erase-core は呼び手が必要に応じて
;; 掛ける。span を落としてから返すと、診断の primary span が指す位置を
;; 呼び手が復元できない。
(struct compiled (core type row callables) #:transparent)

(define (compile-source/string source-id str #:expansion-context [ctx (hash)])
  (compile-source source-id (string->bytes/utf-8 str)
                  #:expansion-context ctx))

;; spec §6。診断は最初に落ちた段のものを 1 件だけ返す。parse と
;; lower-surface は診断を受け取ると素通しするため、段ごとの場合分けは
;; elab の手前まで要らない。
(define (compile-source source-id bytes #:expansion-context [ctx (hash)])
  (define low (lower-surface (parse (lex source-id bytes)) (current-trait-env)))
  (cond
    [(diagnostic? low) low]
    [else
     (define result (elab (lowered-term low) #:expansion-context ctx))
     (match result
       [`(err ,d) d]
       [(list core type row callables) (compiled core type row callables)])]))
