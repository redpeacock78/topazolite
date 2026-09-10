#lang racket

(require rackunit
         "../ptr-static.rkt"
         "../unsafe-oracle.rkt")

;; unsafe.md §5.3。Unsafe の内側の redex だけを拾う。
(test-case "unsafe-raw-redex は Unsafe の内側だけを拾う（unsafe.md §5.3）"
  (define (cfg-of c)
    `(cfg (Scope (0) ,c) ((0 (resource 1000))) ((0 Available)) () ()))
  (define p '(PtrVal 0 () Const (Prov owned)))
  (check-equal? (unsafe-raw-redex (cfg-of `(Unsafe (RawLoad ,p)))) 'raw-load)
  (check-equal? (unsafe-raw-redex (cfg-of `(Unsafe (RawStore ,p 1)))) 'raw-store)
  (check-equal? (unsafe-raw-redex (cfg-of `(Unsafe (PtrOffset ,p 1)))) 'ptr-offset)
  (check-equal? (unsafe-raw-redex (cfg-of `(Unsafe (FromRawPtr ,p 0)))) 'from-raw-ptr)
  ;; 内側の raw 操作が次の redex であるとき、外側の RawLoad より先に拾う。
  (check-equal? (unsafe-raw-redex
                (cfg-of `(Unsafe (RawLoad (PtrOffset ,p 1)))))
                'ptr-offset)
  (check-equal? (unsafe-raw-redex
                (cfg-of `(Unsafe (RawLoad (FromRawPtr ,p 0)))))
                'from-raw-ptr)
  ;; 逆向きの入れ子でも、実際の次の redex である RawLoad を拾う。
  (check-equal? (unsafe-raw-redex
                (cfg-of `(Unsafe (PtrOffset (RawLoad ,p) 1))))
                'raw-load)
  (check-equal? (unsafe-raw-redex
                (cfg-of `(Unsafe (FromRawPtr (RawLoad ,p) 0))))
                'raw-load)
  ;; Unsafe の外は拾わない。
  (check-false (unsafe-raw-redex (cfg-of `(RawLoad ,p))))
  ;; AddressOf は境界を要求しないため対象外である。
  (check-false (unsafe-raw-redex (cfg-of '(Unsafe (AddressOf (BorrowMutRef 0 () 0))))))
  ;; stuck の判定は未評価 operand も広く拾う。
  (check-equal? (raw-op-under-unsafe?
                (cfg-of '(Unsafe (RawLoad (AddressOf (BorrowMutRef 0 () 0))))))
                'raw-load))

;; unsafe.md §5.3。PtrVal を leaf に持つかを構造で見る。
(test-case "contains-ptrval? が入れ子を辿る（unsafe.md §5.3）"
  (define p '(PtrVal 0 () Const (Prov owned)))
  (check-true (contains-ptrval? p))
  (check-true (contains-ptrval? `(Tuple 1 (Tuple 2 ,p))))
  (check-false (contains-ptrval? '(Tuple 1 (Tuple 2 3))))
  (check-false (contains-ptrval? 'x)))

;; unsafe.md §3.2 と §3.3 の表を独立に写したものである。
(test-case "oracle-obligations が 4 つの操作を持つ（unsafe.md §3.2、§3.3）"
  (check-equal? (sort (oracle-obligations 'raw-load) symbol<?)
                '(Aligned AliveAllocation InBounds Initialized NonNull Readable))
  (check-equal? (sort (oracle-obligations 'raw-store) symbol<?)
                '(Aligned AliveAllocation InBounds NonNull Writable))
  (check-equal? (sort (oracle-obligations 'ptr-offset) symbol<?)
                '(AliveAllocation InBounds))
  (check-equal? (sort (oracle-obligations 'from-raw-ptr) symbol<?)
                '(Aligned AliveAllocation Initialized LifetimeValid NonNull))
  (check-false (oracle-obligations 'address-of)))

(test-case "ucounters の初期値（unsafe.md §5.3）"
  (check-equal? (length (ucounters-zeros (make-ucounters))) 7))

(define empty-sidecar (ptr-sidecar '()))

(define full-sidecar
  (ptr-sidecar
   (for/list ([k (in-list '(raw-load raw-store ptr-offset from-raw-ptr))])
     (ptr-request k '() (oracle-obligations k) #t))))

(define (fails-with config sidecar expected)
  (define outcome (check-unsafe-execution config sidecar 200 (make-ucounters)))
  (check-true (and (pair? outcome) (eq? (first outcome) 'fail))
              (format "fail を期待した: ~s" outcome))
  (check-equal? (second outcome) expected))

(define ptr '(PtrVal 0 () Const (Prov owned)))

;; 条件 1。Unsafe の外の RawLoad は落ちる。
(test-case "Unsafe の外の RawLoad が落ちる（unsafe.md §5.3）"
  (fails-with `(cfg (Scope (0) (RawLoad ,ptr))
                    ((0 (resource 1000))) ((0 Available)) () ())
              full-sidecar 'raw-outside-unsafe))

;; 条件 2。静的側に記録の無い raw 操作は落ちる。
(test-case "静的側に記録の無い raw 操作が落ちる（unsafe.md §5.3）"
  (fails-with `(cfg (Scope (0) (Unsafe (RawLoad ,ptr)))
                    ((0 (resource 1000))) ((0 Available)) () ())
              empty-sidecar 'obligation-mismatch))

;; 条件 3。Unsafe が PtrVal を返すと落ちる。
(test-case "Unsafe が PtrVal を返すと落ちる（unsafe.md §5.3）"
  (fails-with `(cfg (Scope (0) (Unsafe ,ptr))
                    ((0 (resource 1000))) ((0 Available)) () ())
              full-sidecar 'ptrval-escapes-unsafe))

;; 条件 4。Unsafe の内側の Yield が PtrVal を観測すると落ちる。
;; R-Yield は実際に発火し、θ へ (obs (PtrVal ...)) を足す。
(test-case "Unsafe の内側で PtrVal を観測すると落ちる（unsafe.md §5.3）"
  (fails-with `(cfg (Scope (0) (Unsafe (Yield ,ptr 1)))
                    ((0 (resource 1000))) ((0 Available)) () ())
              full-sidecar 'ptrval-in-observation))

;; 条件 5。Unsafe の内側の stuck は受理し、カウンタを進める。
(test-case "Unsafe の内側の stuck は受理する（unsafe.md §5.3）"
  (define counters (make-ucounters))
  (check-equal? (check-unsafe-execution
                 `(cfg (Scope (0) (Unsafe (RawLoad ,ptr)))
                       ((0 (resource 1000))) ((0 Moved)) () ())
                 full-sidecar 200 counters)
                'ok)
  (check-equal? (ucounters-stuck-in-unsafe counters) 1))

;; 条件 5。Unsafe の外の stuck は落ちる。
(test-case "Unsafe の外の stuck が落ちる（unsafe.md §5.3）"
  (fails-with `(cfg (Scope (0) (RawLoad ,ptr))
                    ((0 (resource 1000))) ((0 Moved)) () ())
              full-sidecar 'stuck-outside-unsafe))
