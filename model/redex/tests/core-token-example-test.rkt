#lang racket
;; [REQ: OWN-009]
(require rackunit
         racket/file
         racket/match
         racket/runtime-path
         racket/set
         "../borrow.rkt"
         "../gen.rkt"
         "../machine.rkt"
         "../typing.rkt")

(define-runtime-path core-token-fst "../../fstar/Topazolite.Core.Token.fst")

;; 例ごとに開始構成、規則から手で導いた期待値を置く。
(define token-examples
  (list
   (list "example_delta_acquire"
         '(cfg (Apply (PrimVal (Reserved o-acquire) acquire) 7) () () () ())
         'R-Delta '(Owned Res)
         '(OwnedLeaf (tok 0) (resource 7))
         '() '(((tok 0) Available))
         '() '((tok 0))
         '() '())
   (list "example_ownleaf_fresh"
         '(cfg (Scope () (OwnLeaf (resource 1))) () () () ())
         'R-OwnLeaf '(Owned Res)
         '(Scope () (OwnedLeaf (tok 0) (resource 1)))
         '() '(((tok 0) Available))
         '() '((tok 0))
         '() '())
   (list "example_ownleaf_pass"
         '(cfg (Scope () (OwnLeaf (OwnedLeaf (tok 4) (resource 1))))
              () () (((tok 4) Available)) ())
         'R-OwnLeafPass '(Owned Res)
         '(Scope () (OwnedLeaf (tok 4) (resource 1)))
         '(((tok 4) Available)) '(((tok 4) Available))
         '((tok 4)) '((tok 4))
         '() '())
   (list "example_ownleaf_transit"
         '(cfg (Scope ()
                (OwnLeaf
                 (OwnedTransit 0
                   (Construct (Option (Owned Res)) some
                     (OwnedLeaf (tok 4) (resource 1))))))
              ((0 (Construct (Option (Owned Res)) some
                    (OwnedLeaf (tok 4) (resource 1)))
                  (declared (Owned (Option (Owned Res))))))
              ((0 Moved)) (((tok 4) Available)) ())
         'R-OwnLeafTransit '(Owned (Option (Owned Res)))
         '(Scope ()
            (OwnedTransit 0
              (Construct (Option (Owned Res)) some
                (OwnedLeaf (tok 4) (resource 1)))))
         '(((tok 4) Available)) '(((tok 4) Available))
         '((tok 4)) '((tok 4))
         '() '())))

(define (configuration-control configuration)
  (match configuration [`(cfg ,control ,_ ...) control]))

(define (configuration-token-set configuration)
  (match configuration
    [`(cfg ,_ ,_ ,_ ,tokens ,_) (list->set tokens)]))

(define (configuration-structural-tokens configuration)
  (match configuration
    [`(cfg ,control ,heap ,states ,_ ,_)
     (structural-tokens control heap states)]))

(define (configuration-observed-tokens configuration)
  (match configuration [`(cfg ,_ ,_ ,_ ,_ ,trace) (observed-tokens trace)]))

(define (check-configuration-valid configuration expected name phase)
  (define row (runtime-row configuration '() expected))
  (check-not-false row (format "~a ~a: runtime-row が無い" name phase))
  (when row
    (check-true (config-ok? configuration '() expected row)
                (format "~a ~a: config-ok? が偽" name phase))))

(for ([example (in-list token-examples)])
  (match-define
    (list name start expected-rule expected-type expected-control
          expected-ledger-before expected-ledger-after
          expected-structural-before expected-structural-after
          expected-observed-before expected-observed-after)
    example)
  (test-case (format "~a: 規則、構成検査、token 射影" name)
    (check-configuration-valid start expected-type name "before")
    (define successors (raw-steps-g2/named start))
    (check-equal? (length successors) 1
                  (format "~a: 一意な一手" name))
    (when (= (length successors) 1)
      (match-define (list actual-rule after) (first successors))
      (check-eq? actual-rule expected-rule (format "~a: rule" name))
      (check-equal? (configuration-control after) expected-control
                    (format "~a: control after" name))
      (check-configuration-valid after expected-type name "after")
      (check-equal? (configuration-token-set start)
                    (list->set expected-ledger-before)
                    (format "~a: ledger before" name))
      (check-equal? (configuration-token-set after)
                    (list->set expected-ledger-after)
                    (format "~a: ledger after" name))
      (check-equal? (configuration-structural-tokens start)
                    expected-structural-before
                    (format "~a: structural tokens before" name))
      (check-equal? (configuration-structural-tokens after)
                    expected-structural-after
                    (format "~a: structural tokens after" name))
      (check-equal? (configuration-observed-tokens start)
                    expected-observed-before
                    (format "~a: observed tokens before" name))
      (check-equal? (configuration-observed-tokens after)
                    expected-observed-after
                    (format "~a: observed tokens after" name)))))

(test-case "Redex の例名は F* の AUX example と一致する"
  (define fstar-names
    (regexp-match*
     #px"//@ AUX: example OWN-009\n(?:let|val) ([a-z_]+)"
     (file->string core-token-fst)
     #:match-select cadr))
  (check-equal? (list->set fstar-names)
                (list->set (map first token-examples))))
