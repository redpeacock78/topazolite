#lang racket

(require rackunit
         racket/list
         racket/match
         "../diagnostic.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../machine.rkt"
         "../region.rkt"
         "../typing.rkt"
         "../elaborate.rkt")

(define resource-list '(List (Owned Res)))

(define source
  `(Apply
    (Fn ((items ,resource-list)) Unit (Partial Own)
      (Recur walk ((rest ,resource-list)) Unit (Partial Own)
        (Eliminate (Move rest)
          ((nil () -> unit)
           (cons (head tail) ->
             (Apply walk (Move tail)))))
        (Apply walk (Move items))))
    (Construct cons (Types (Owned Res))
      (Apply acquire 1)
      (Construct cons (Types (Owned Res))
        (Apply acquire 2)
        (Construct nil (Types (Owned Res)))))))

(define (elaborated-source)
  (match (elab source)
    [(list core expected _row callables)
     (values (execution-core (erase-core core) callables)
             expected callables)]
    [other (fail-check (format "UCore を elaborate できない: ~s" other))]))

(define (run-source)
  (define-values (core expected callables) (elaborated-source))
  (define run (bounded-trace-g2 (inject-g2m core) 500))
  (check-equal? (execution-outcome run) 'terminal)
  (values (execution-configs run) expected callables core))

(define (first-recur-unfold configs)
  (for/or ([configuration (in-list configs)])
    (for/or ([step (in-list (raw-steps-g2/named configuration))])
      (and (eq? (first step) 'R-RecurUnfold) (second step)))))

(define (cons-branches term)
  (let walk ([value (erase-core term)])
    (match value
      [`(Eliminate ,scrutinee (,arms ...))
       (append
        (for/list ([arm (in-list arms)]
                   #:when (match arm [`(cons (,head ,tail) -> ,_) #t] [_ #f]))
          (match arm [`(cons (,head ,tail) -> ,body) (list head tail body)]))
        (walk scrutinee)
        (append* (for/list ([arm (in-list arms)]) (walk (last arm)))))]
      [(? pair? parts) (append* (map walk parts))]
      [_ '()])))

(define (first-recurval term)
  (let walk ([value (erase-core term)])
    (match value
      [`(RecurVal ,_ ,_ ,_ ,_) value]
      [(? pair? parts) (for/or ([part (in-list parts)]) (walk part))]
      [_ #f])))

(define (capture-in-recurval term captured)
  (let walk ([value term])
    (match value
      [`(RecurVal ,callable ,function (,parameters ...) ,body)
       (define (insert-after-parameter-lets core)
        (match core
          [`(Scope ,managed ,inner)
           `(Scope ,managed ,(insert-after-parameter-lets inner))]
          [`(Let ,binder ,bound ,next)
            #:when (ormap (lambda (parameter)
                            (equal? (erase-core bound)
                                    (erase-core parameter)))
                          parameters)
            `(Let ,binder ,bound ,(insert-after-parameter-lets next))]
           [_ `(Let (capture-probe let Unit)
                    (Drop (Move ,captured))
                    ,core)]))
       (and captured
            `(RecurVal ,callable ,function ,parameters
                       ,(insert-after-parameter-lets body)))]
      [(? pair? parts)
       (for/or ([part (in-list parts)]) (walk part))]
      [_ #f])))

(define (capture-in-cons-branch term)
  (define changed? #f)
  (define (walk value)
    (if changed?
        value
        (match value
          [`(Eliminate ,scrutinee (,arms ...))
           (define index
             (for/first ([arm (in-list arms)] [i (in-naturals)]
                         #:when
                         (match arm
                           [`(cons (,_ ,_) -> ,body)
                            (and (first-recurval body) #t)]
                           [_ #f]))
               i))
           (if index
               (begin
                 (set! changed? #t)
                 `(Eliminate ,scrutinee
                   ,(for/list ([arm (in-list arms)] [i (in-naturals)])
                      (if (= i index)
                          (match arm
                            [`(cons (,head ,tail) -> ,body)
                             (define injected
                               (for/or ([captured (in-list (list head tail))])
                                 (define candidate
                                   (capture-in-recurval body captured))
                                 (and candidate
                                      (let ([recurval (first-recurval candidate)])
                                        (and recurval
                                             (set-member? (core-free-vars recurval)
                                                          captured)
                                             candidate)))))
                             (and injected
                                  `(cons (,head ,tail) -> ,injected))])
                          arm))))
               `(Eliminate ,(walk scrutinee)
                 ,(for/list ([arm (in-list arms)])
                    (match arm
                      [`(,_ ,_ -> ,body) (append (drop-right arm 1)
                                                 (list (walk body)))]
                      [_ arm]))))]
          [(? pair? parts) (map walk parts)]
          [_ value])))
  (walk (erase-core term)))

;; RecurUnfold 後に消えた branch の canonical Let を補い、同じ raw-use 検査を当てる。
(define (resource-branch-encoding-failure-key control)
  (for/or ([branch (in-list (cons-branches control))])
    (match branch
      [(list head tail body)
       (define inner
         (match body [`(Scope () ,scoped) scoped] [_ body]))
       (define canonical
         (if (equal? body `(Scope () ,inner))
             inner
             `(Let (,(gensym 'probe-head) let (Owned Res)) ,head
                (Let (,(gensym 'probe-tail) let ,resource-list) ,tail
                  ,inner))))
       (let/ec escape
         (check-owned-encoding
          (list head tail)
          (list '(Owned Res) resource-list)
          canonical 'probe
          (lambda (key . _) (escape key))
          #:missing-key (lambda (_) 'resource-binder-missing-binding)
          #:raw-key (lambda (_) 'resource-binder-raw-misuse))
         #f)]
      [_ #f])))

(define (replace-control configuration control)
  (match configuration
    [`(cfg ,_ ,heap ,places ,tokens ,trace)
     `(cfg ,control ,heap ,places ,tokens ,trace)]))

(test-case "B5 資源 List の再帰走査の全中間 config が型付く"
  (define-values (configs expected callables _core) (run-source))
  (check-not-false
   (for/or ([configuration (in-list configs)])
     (for/or ([step (in-list (raw-steps-g2/named configuration))])
       (eq? (first step) 'R-RecurUnfold))))
  (check-true (pair? configs))
  (for ([configuration (in-list configs)] [index (in-naturals)])
    (define row (runtime-row configuration callables expected))
    (check-not-false
     row (format "config ~a に runtime-row がある: ~s" index configuration))
    (check-true (and row (config-ok? configuration callables expected row))
                (format "config ~a が型付く: ~s" index configuration)))
  (define terminal (last configs))
  (check-equal? (map second (config-tokens terminal)) '(Dropped Dropped)))

(test-case "B5n RecurVal 内の free capture は E-OWN-035 で拒否する"
  (define-values (configs expected callables _core) (run-source))
  (define baseline (first-recur-unfold configs))
  (check-not-false baseline "R-RecurUnfold 直後の config がある")
  (when baseline
    (define baseline-row (runtime-row baseline callables expected))
    (check-not-false baseline-row "基準 config の runtime-row がある")
    (check-true (and baseline-row
                     (config-ok? baseline callables expected baseline-row))
                "基準 config は型付く")
    (define mutated-control (capture-in-cons-branch (config-core baseline)))
    (check-not-false mutated-control "RecurVal を含む cons 枝に tail capture を入れた")
    (when mutated-control
      (define mutated (replace-control baseline mutated-control))
      (check-false (config-ok? mutated callables expected baseline-row))
      (check-false (resource-branch-encoding-failure-key
                    (config-core baseline)))
      (check-equal? (resource-branch-encoding-failure-key mutated-control)
                    'resource-binder-raw-misuse))))
