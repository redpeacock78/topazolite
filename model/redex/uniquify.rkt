#lang racket

(provide uniquify-binders binder-base binder-has-identifier?
         core-binder-symbols (struct-out exn:fail:uniquify))

(require racket/match)

(struct exn:fail:uniquify exn:fail () #:transparent)

(define open-mark "⟨")
(define close-mark "⟩")
(define identifier-rx
  (pregexp (format "~a[0-9]+~a$" open-mark close-mark)))

;; 末尾の ⟨N⟩ を 1 つだけ剥がす。substitute が付ける «N» には当たらないので、
;; 簡約を通った束縛子へ使うときは borrow-oracle.rkt の normalize-binder を
;; 先に通す。表示のための剥がしは diagnostic-render.rkt の strip-identifiers
;; が両方を担う。
(define (binder-base symbol)
  (string->symbol
   (regexp-replace identifier-rx (symbol->string symbol) "")))

(define (binder-has-identifier? symbol)
  (and (symbol? symbol)
       (regexp-match? identifier-rx (symbol->string symbol))))

(define (uniquify-binders core)
  (define counter 0)

  (define (fresh-for symbol)
    (set! counter (add1 counter))
    (string->symbol
     (format "~a~a~a~a" symbol open-mark counter close-mark)))

  (define (rename environment symbol)
    (hash-ref environment symbol symbol))

  (define (binder-form? term)
    (match term
      [`(#:bind ,_ ,_) #t]
      [_ #f]))

  (define (bind-all environment binders)
    (for/fold ([renamed '()]
               [extended environment]
               #:result (values (reverse renamed) extended))
              ([binder (in-list binders)])
      (match binder
        [`(#:bind ,symbol ,span)
         (define renamed-symbol (fresh-for symbol))
         (values (cons `(#:bind ,renamed-symbol ,span) renamed)
                 (hash-set extended symbol renamed-symbol))]
        [_
         (raise
          (exn:fail:uniquify
           (format "unknown binder form: ~s" binder)
           (current-continuation-marks)))])))

  (define (walk environment term)
    (match term
      [`(Lam ,span ,origin ,callable ,parameters ,body)
       (define-values (renamed extended)
         (bind-all environment parameters))
       `(Lam ,span ,origin ,callable ,renamed ,(walk extended body))]

      ;; G2+ の binding mode 付き Let。bound は scope 外である。
      [`(Let ,span (,binder ,mode ,type) ,bound ,body)
       (define bound* (walk environment bound))
       (define-values (renamed extended)
         (bind-all environment (list binder)))
       `(Let ,span (,(first renamed) ,mode ,type)
             ,bound* ,(walk extended body))]

      ;; G1 の Let。
      [`(Let ,span (,binder ,type) ,bound ,body)
       (define bound* (walk environment bound))
       (define-values (renamed extended)
         (bind-all environment (list binder)))
       `(Let ,span (,(first renamed) ,type)
             ,bound* ,(walk extended body))]

      ;; Eliminate の branch。構成子の引数が branch body の scope に入る。
      [`(,span ,constructor ,parameters -> ,body)
       #:when (list? parameters)
       (define-values (renamed extended)
         (bind-all environment parameters))
       `(,span ,constructor ,renamed -> ,(walk extended body))]

      ;; Handle の handler。
      [`(,span ,binder -> ,body)
       #:when (binder-form? binder)
       (define-values (renamed extended)
         (bind-all environment (list binder)))
       `(,span ,(first renamed) -> ,(walk extended body))]

      ;; Recur の関数名は body と continuation の双方に見える。
      [`(Recur ,span ,callable ,function ,parameters ,body ,continuation)
       (define-values (renamed-function with-function)
         (bind-all environment (list function)))
       (define-values (renamed-parameters extended)
         (bind-all with-function parameters))
       `(Recur ,span ,callable ,(first renamed-function)
               ,renamed-parameters
               ,(walk extended body)
               ,(walk with-function continuation))]

      [`(RecurVal ,span ,callable ,function ,parameters ,body)
       (define-values (renamed-function with-function)
         (bind-all environment (list function)))
       (define-values (renamed-parameters extended)
         (bind-all with-function parameters))
       `(RecurVal ,span ,callable ,(first renamed-function)
                  ,renamed-parameters ,(walk extended body))]

      [`(#:var ,symbol ,span)
       `(#:var ,(rename environment symbol) ,span)]

      ;; 既知の束縛形は bind-all が #:bind を消費する。ここへ届く形は
      ;; span-core.rkt の閉じた束縛形一覧に漏れがあるため、黙って通さない。
      [(cons '#:bind _)
       (raise
        (exn:fail:uniquify
         (format "未知の束縛形に #:bind がある: ~s" term)
         (current-continuation-marks)))]

      [(? list?)
       (map (lambda (child) (walk environment child)) term)]
      [_ term]))

  (walk (hash) core))

(define (core-binder-symbols core)
  (define (walk term acc)
    (match term
      [`(#:bind ,symbol ,_) (cons symbol acc)]
      [(? list?)
       (for/fold ([result acc]) ([child (in-list term)])
         (walk child result))]
      [_ acc]))
  (reverse (walk core '())))
