#lang racket

(require rackunit racket/match
         "../ptr-static.rkt"
         "../region.rkt"
         "../borrow.rkt"
         "../search.rkt"
         "../typing.rkt")

;; rawptr-typing-test.rkt と同じ形で Λ を組む。借用を含む項は region IR が
;; 無いと borrow-unknown-owner-region で落ちる。
(define (Λ-of ir) (region-ctx ir '() (hash) (hash)))

(define (ptr-sidecar-of core)
  (define ir (build-region-ir core))
  (match (type-of/raw*+ptr core '() '() '() (Λ-of ir))
    [(list 'ok (list _τ _ε sidecar)) sidecar]
    [other (error 'ptr-sidecar-of "型検査が受理しない: ~s" other)]))

;; rawptr-typing-test.rkt の in-scope をそのまま写す。
(define (in-scope body)
  `(Scope ()
     (Let (x let (Owned Res)) (resource 1) ,body)))

;; unsafe.md §5.2。Unsafe の内側の RawLoad が obligation ごと記録される。
(test-case "RawLoad の出現が sidecar へ入る（unsafe.md §5.2）"
  (define sidecar
    (ptr-sidecar-of (in-scope '(Unsafe (RawLoad (AddressOf (BorrowMut x)))))))
  (define kinds (map ptr-request-kind (ptr-sidecar-requests sidecar)))
  (check-true (and (memq 'raw-load kinds) #t) "raw-load が記録される")
  (check-equal? (ptr-sidecar-obligations sidecar 'raw-load)
                (raw-load-obligation-ids))
  ;; Unsafe の内側なので unsafe? は真になる。
  (for ([r (in-list (ptr-sidecar-requests sidecar))])
    (check-true (ptr-request-unsafe? r) (format "~s" (ptr-request-kind r)))))

;; 出現の無い kind は #f を返す。fail-closed な既定である。
(test-case "出現の無い kind は #f（unsafe.md §5.2）"
  ;; 所有束縛は Move で消費し、raw 操作を含まない項にする。
  (define sidecar (ptr-sidecar-of (in-scope '(Move x))))
  (check-false (ptr-sidecar-obligations sidecar 'raw-store)))
