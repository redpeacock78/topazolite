#lang racket

(require "lexer.rkt"
         "parser.rkt"
         "surface-lower.rkt"
         "elaborate.rkt"
         "diagnostic.rkt"
         (only-in "origins.rkt"
                  call-with-trait-ledger
                  make-trait-ledger
                  current-trait-ledger
                  trait-ledger-env)
         (only-in "traits.rkt"
                  make-trait-env
                  trait-env-trait-rows
                  trait-env-impl-rows
                  trait-env-intersect-rows
                  trait-env-scope-rows))

(provide compile-source compile-source/string (struct-out compiled))

;; spec §5。成功の成果物である。欄は elab の返り値の後ろへ台帳を足す。
;; core は span を持つ Typed Core であり、erase-core は呼び手が必要に応じて
;; 掛ける。span を落としてから返すと、診断の primary span が指す位置を
;; 呼び手が復元できない。
(struct compiled (core type row callables ledger) #:transparent)

(define (compile-source/string source-id str #:expansion-context [ctx (hash)])
  (compile-source source-id (string->bytes/utf-8 str)
                  #:expansion-context ctx))

;; spec §6。診断は最初に落ちた段のものを 1 件だけ返す。
(define (make-ledger-fail low)
  ;; 行は span を持たないので、衝突した鍵から原文の span を引く。
  ;; 衝突は必ず宣言が足した鍵を含むので、spans が必ず引ける。
  (λ (reason kind key)
    (define span
      (hash-ref (lowered-spans low) (cons kind key)
                (λ () (error 'compile-source "span の無い衝突: ~s ~s" kind key))))
    (diagnostic-of 'surface reason #:primary-span span)))

(define (compile-source source-id bytes #:expansion-context [ctx (hash)])
  (define base-ledger (current-trait-ledger))
  (define base (trait-ledger-env base-ledger))
  (define low (lower-surface (parse (lex source-id bytes)) base))
  (define (elab-under ledger)
    (call-with-trait-ledger
     ledger
     (λ ()
       (match (elab (lowered-term low) #:expansion-context ctx)
         [`(err ,d) d]
         [(list core type row callables)
          (compiled core type row callables ledger)]))))
  (cond
    [(diagnostic? low) low]
    [(and (null? (lowered-trait-rows low))
          (null? (lowered-impl-rows low))
          (null? (lowered-intersect-rows low)))
     ;; 宣言が無ければ外側の台帳を eq? のまま使い、キャッシュを止めない（spec §6.6）。
     (elab-under base-ledger)]
    [else
     (define fail (make-ledger-fail low))
     (define env
       (make-trait-env
        #:trait (append (trait-env-trait-rows base) (lowered-trait-rows low))
        #:impl (append (trait-env-impl-rows base) (lowered-impl-rows low))
        #:intersect (append (trait-env-intersect-rows base)
                            (lowered-intersect-rows low))
        #:scope (trait-env-scope-rows base)
        #:fail fail))
     (cond
       [(diagnostic? env) env]
       [else
        (define ledger (make-trait-ledger env #:fail fail))
        (if (diagnostic? ledger) ledger (elab-under ledger))])]))
