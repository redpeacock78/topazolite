#lang racket

(require rackunit
         racket/match
         "../diagnostic.rkt"
         "../driver.rkt"
         "../erase.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../span-core.rkt")

(define (compile source) (compile-source/string 'src source))

(define (compile-accepted source)
  (define result (compile source))
  (check-true (compiled? result)
              (if (diagnostic? result)
                  (format "~a: ~a" (diagnostic-id result)
                          (diagnostic-message result))
                  (format "unexpected result: ~s" result)))
  (and (compiled? result) result))

(define (trace-g2 compiled)
  (call-with-trait-ledger
   (compiled-ledger compiled)
   (lambda ()
     (let loop ([current (inject-g2m
                          (erase-core (compiled-execution-core compiled)))]
                [configs '()]
                [rules '()]
                [fuel 10000])
       (when (zero? fuel)
         (error 'trace-g2 "評価 fuel を使い切った: ~s" current))
       (define next (raw-steps-g2/named current))
       (match next
         ['() (values (append configs (list current)) rules)]
         [(list (list rule config))
          (loop config (append configs (list current))
                (append rules (list rule)) (sub1 fuel))]
         [_ (fail (format "一意な次状態を期待した: ~s" next))])))))

(define (config-tokens config)
  (match config [`(cfg ,_ ,_ ,_ ,tokens ,_) tokens]))

(define (config-events config)
  (match config [`(cfg ,_ ,_ ,_ ,_ ,events) events]))

(define (check-no-available-tokens terminal)
  (for ([entry (in-list (config-tokens terminal))])
    (match entry
      [(list _ 'Available) (fail (format "終端に Available token が残る: ~s" entry))]
      [_ (void)])))

(define (fin-leaf-events terminal)
  (filter (lambda (event) (match event [`(finLeaf ,_ ,_) #t] [_ #f]))
          (config-events terminal)))

(define (core-forms predicate term)
  (define (walk value)
    (append (if (predicate value) (list value) '())
            (if (pair? value) (append-map walk value) '())))
  (walk term))

(define (owned-some-fields core)
  (core-forms
   (lambda (term)
     (match (peel-node term)
       [`(Construct ,type some ,_)
        (match (peel-ty type)
          [`(Option (Owned ,_)) #t]
          [_ #f])]
       [_ #f]))
   core))

(define for-source
  (string-append
   "fn main() -> Unit ! Own {\n"
   " let xs: List<Int> = cons(1, nil())\n"
   " let r = for x in xs { leave acquire(1) }\n"
   " ()\n"
   "}\nmain()"))

(define (if-source argument)
  (string-append
   "fn f(c: Bool) -> Unit ! Own {\n"
   " let r = if c { leave acquire(1) }\n"
   " ()\n"
   "}\nf(" argument ")"))

(test-case "B1 式位置の for の leave で資源を返す"
  (define compiled (compile-accepted for-source))
  (when compiled
    (define-values (configs _rules) (trace-g2 compiled))
    (define terminal (last configs))
    (check-no-available-tokens terminal)
    (check-equal? (length (fin-leaf-events terminal)) 1)))

(test-case "B2 else の無い if の leave は true のときだけ資源を発行する"
  (define true-result (compile-accepted (if-source "true")))
  (when true-result
    (define-values (configs _rules) (trace-g2 true-result))
    (define terminal (last configs))
    (check-no-available-tokens terminal)
    (check-equal? (length (fin-leaf-events terminal)) 1))
  (define false-result (compile-accepted (if-source "false")))
  (when false-result
    (define-values (configs _rules) (trace-g2 false-result))
    (define terminal (last configs))
    (check-no-available-tokens terminal)
    (check-equal? (length (fin-leaf-events terminal)) 0)
    (check-equal? (config-tokens terminal) '())))

(test-case "B3 leave の some 欄は OwnLeaf で包み token producer は一度"
  (for ([compiled (in-list (filter values
                                   (list (compile-accepted for-source)
                                         (compile-accepted (if-source "true")))))])
    (define fields (owned-some-fields (compiled-execution-core compiled)))
    (check-not-false (pair? fields))
    (for ([construct (in-list fields)])
      (match (peel-node construct)
        [`(Construct ,_ some ,field)
         (check-true (match (peel-node field) [`(OwnLeaf ,_) #t] [_ #f]))]))
    (define-values (configs rules) (trace-g2 compiled))
    (define terminal (last configs))
    (check-equal? (count (lambda (rule) (eq? rule 'R-OwnLeafPass)) rules) 1)
    (check-equal? (count (lambda (rule) (eq? rule 'R-OwnLeaf)) rules) 0)
    (check-equal? (length (config-tokens terminal)) 1)
    (check-equal? (length (fin-leaf-events terminal)) 1)))

(test-case "B4 非資源の leave の実行 Core は HEAD と同じ"
  (for ([source+expected
         (in-list
          (list
           (list
            "fn f(xs: List<Int>) -> Option<Int> { return for x in xs { leave 1 } }\nf(cons(1, nil))"
            (string-append
             "(Recur callable0 f⟨1⟩ (xs⟨2⟩) (Handle (Return boundary0 (Option Int)) (return-value⟨3⟩ -> return-value⟨3⟩) (Scope () (Let (%stmt⟨13⟩ const Never) (Perform (Return boundary0 (Option Int)) (Let (%for-list-44⟨4⟩ const (List Int)) xs⟨2⟩ (Handle (Return boundary1 (Option Int)) (return-value⟨5⟩ -> return-value⟨5⟩) (Scope () (Let (%for-option-44⟨12⟩ const Unit) (Recur callable1 %for-loop-44⟨6⟩ (%for-rest-44⟨7⟩) (Eliminate %for-rest-44⟨7⟩ ((nil () -> unit) (cons (x⟨8⟩ %for-tail-44⟨9⟩) -> (Let (%stmt⟨11⟩ const Unit) (Let (%stmt⟨10⟩ const Never) (Perform (Return boundary1 (Option Int)) (Construct (Option Int) some 1)) unit) (Apply %for-loop-44⟨6⟩ %for-tail-44⟨9⟩))))) (Apply %for-loop-44⟨6⟩ %for-list-44⟨4⟩)) (Construct (Option Int) none)))))) unit))) (Apply f⟨1⟩ (Construct (List Int) cons 1 (Construct (List Int) nil))))"))
           (list
            "fn f(c: Bool) -> Option<Int> { return if c { leave 1 } }\nf(true)"
            (string-append
             "(Recur callable0 f⟨1⟩ (c⟨2⟩) (Handle (Return boundary0 (Option Int)) (return-value⟨3⟩ -> return-value⟨3⟩) (Scope () (Let (%stmt⟨6⟩ const Never) (Perform (Return boundary0 (Option Int)) (Let (%ifcond-option⟨4⟩ const Bool) c⟨2⟩ (Handle (Return boundary1 (Option Int)) (return-value⟨5⟩ -> return-value⟨5⟩) (Scope () (Eliminate %ifcond-option⟨4⟩ ((true () -> (Construct (Option Int) some (Perform (Return boundary1 (Option Int)) (Construct (Option Int) some 1)))) (false () -> (Construct (Option Int) none)))))))) unit))) (Apply f⟨1⟩ (Construct Bool true)))"))))])
    (define compiled (compile-accepted (first source+expected)))
    (when compiled
      (check-equal? (format "~s" (compiled-execution-core compiled))
                    (second source+expected)))))
