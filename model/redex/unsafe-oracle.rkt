#lang racket

(require racket/match
         redex/reduction-semantics
         "lang.rkt"
         "machine.rkt"
         "ptr-static.rkt")

;; unsafe.md §5.3。性質 9 の oracle。
;; typing.rkt を require しない。判定を借りると条件 2 が恒真になる。
(provide (struct-out ucounters)
         make-ucounters
         ucounters-zeros
         raw-op-under-unsafe?
         unsafe-raw-redex
         yield-under-unsafe?
         contains-ptrval?
         oracle-obligations
         check-unsafe-execution)

(struct ucounters (raw-load raw-store ptr-offset from-raw-ptr
                   unsafe-exit yield-in-unsafe stuck-in-unsafe)
  #:mutable #:transparent)

(define (make-ucounters) (ucounters 0 0 0 0 0 0 0))

(define counter-names
  '(raw-load raw-store ptr-offset from-raw-ptr
    unsafe-exit yield-in-unsafe stuck-in-unsafe))

(define (counter-ref counters name)
  (case name
    [(raw-load) (ucounters-raw-load counters)]
    [(raw-store) (ucounters-raw-store counters)]
    [(ptr-offset) (ucounters-ptr-offset counters)]
    [(from-raw-ptr) (ucounters-from-raw-ptr counters)]
    [(unsafe-exit) (ucounters-unsafe-exit counters)]
    [(yield-in-unsafe) (ucounters-yield-in-unsafe counters)]
    [(stuck-in-unsafe) (ucounters-stuck-in-unsafe counters)]))

(define (bump! counters name)
  (case name
    [(raw-load) (set-ucounters-raw-load! counters (add1 (ucounters-raw-load counters)))]
    [(raw-store) (set-ucounters-raw-store! counters (add1 (ucounters-raw-store counters)))]
    [(ptr-offset) (set-ucounters-ptr-offset! counters (add1 (ucounters-ptr-offset counters)))]
    [(from-raw-ptr) (set-ucounters-from-raw-ptr! counters (add1 (ucounters-from-raw-ptr counters)))]
    [(unsafe-exit) (set-ucounters-unsafe-exit! counters (add1 (ucounters-unsafe-exit counters)))]
    [(yield-in-unsafe) (set-ucounters-yield-in-unsafe! counters (add1 (ucounters-yield-in-unsafe counters)))]
    [(stuck-in-unsafe) (set-ucounters-stuck-in-unsafe! counters (add1 (ucounters-stuck-in-unsafe counters)))]))

(define (ucounters-zeros counters)
  (for/list ([n (in-list counter-names)] #:when (zero? (counter-ref counters n)))
    n))

;; config は (cfg c H Ω Λtok θ) の 6 要素である。
(define (config-control c) (second c))
(define (config-trace c) (list-ref c 5))

(define (control-term c)
  (if (and (pair? c) (eq? (car c) 'cfg))
      (config-control c)
      c))

;; stuck の許容判定は、未評価の operand も含む raw 操作を広く拾う。
(define (raw-op-under-unsafe? c)
  (define control (control-term c))
  (cond
    [(redex-match? G2m (in-hole E_1 (Unsafe (in-hole E_2 (PtrOffset any_1 any_2)))) control) 'ptr-offset]
    [(redex-match? G2m (in-hole E_1 (Unsafe (in-hole E_2 (FromRawPtr any ρ)))) control) 'from-raw-ptr]
    [(redex-match? G2m (in-hole E_1 (Unsafe (in-hole E_2 (RawLoad any)))) control) 'raw-load]
    [(redex-match? G2m (in-hole E_1 (Unsafe (in-hole E_2 (RawStore any_1 any_2)))) control) 'raw-store]
    [else #f]))

;; 評価文脈の分解は一意である。
;; 機械規則と同じ PtrVal の operand へ狭め、入れ子の外側形に依存しないようにする。
(define (unsafe-raw-redex c)
  (define control (control-term c))
  (cond
    [(redex-match? G2m
                   (in-hole E_1
                     (Unsafe (in-hole E_2
                       (PtrOffset (PtrVal p fp ptrmut prov) any_2))))
                   control)
     'ptr-offset]
    [(redex-match? G2m
                   (in-hole E_1
                     (Unsafe (in-hole E_2
                       (FromRawPtr (PtrVal p fp ptrmut prov) ρ))))
                   control)
     'from-raw-ptr]
    [(redex-match? G2m
                   (in-hole E_1
                     (Unsafe (in-hole E_2
                       (RawLoad (PtrVal p fp ptrmut prov)))))
                   control)
     'raw-load]
    [(redex-match? G2m
                   (in-hole E_1
                     (Unsafe (in-hole E_2
                       (RawStore (PtrVal p fp ptrmut prov) any_2))))
                   control)
     'raw-store]
    [else #f]))

(define (yield-under-unsafe? c)
  (and (redex-match? G2m
                    (in-hole E_1 (Unsafe (in-hole E_2 (Yield any_1 any_2))))
                    (control-term c))
       #t))

(define (contains-ptrval? term)
  (let walk ([t term])
    (cond
      [(and (pair? t) (eq? (car t) 'PtrVal)) #t]
      [(pair? t) (or (walk (car t)) (walk (cdr t)))]
      [else #f])))

;; 静的側の表と突き合わせるための、oracle 自身の表。
;; unsafe.md §3.2（RawLoad、RawStore、PtrOffset）と §3.3（FromRawPtr）の
;; 本文から独立に写す。typing.rkt を require して写すと条件 2 が恒真になる。
(define (oracle-obligations kind)
  (case kind
    [(raw-load) '(AliveAllocation NonNull Aligned Initialized Readable InBounds)]
    [(raw-store) '(AliveAllocation NonNull Aligned Writable InBounds)]
    [(ptr-offset) '(AliveAllocation InBounds)]
    [(from-raw-ptr) '(LifetimeValid Aligned Initialized AliveAllocation NonNull)]
    [else #f]))

;; 集合として比べる。表を独立に写す設計である以上、並びの一致まで求めない。
(define (same-obligations? a b)
  (and (list? a) (list? b)
       (equal? (sort a symbol<?) (sort b symbol<?))))

(define (rule-kind name)
  (case name
    [(R-RawLoad) 'raw-load]
    [(R-RawStore) 'raw-store]
    [(R-PtrOffset) 'ptr-offset]
    [(R-FromRawPtrConst R-FromRawPtrMut) 'from-raw-ptr]
    [else #f]))

;; obs.rkt の terminal-kind-g2 は provide されていないため同じ判定を置く。
(define (terminal-control? c)
  (or (redex-match? G2m v c)
      (redex-match? G2m (Error p) c)
      (redex-match? G2m (Perform op v) c)))

;; θ へ足された event。条件 4 が見る観測値はここから取る。
(define (trace-additions current next)
  (define old (config-trace current))
  (define new (config-trace next))
  (for/list ([e (in-list (list-tail new (length old)))]
             #:when (and (pair? e) (eq? (car e) 'obs)))
    (second e)))

(define (check-unsafe-execution config sidecar fuel counters)
  (let loop ([current config] [remaining fuel])
    (cond
      [(zero? remaining) 'discard]
      [else
       (define c (config-control current))
       (define steps (raw-steps-g2/named current))
       (cond
         [(null? steps)
          (cond
            [(terminal-control? c) 'ok]
            [(raw-op-under-unsafe? c) (bump! counters 'stuck-in-unsafe) 'ok]
            [else (list 'fail 'stuck-outside-unsafe current)])]
         [(> (length steps) 1) (list 'fail 'nondeterministic steps)]
         [else
          (match-define (list name next) (first steps))
          (define kind (rule-kind name))
          (cond
            [(and kind (not (eq? (unsafe-raw-redex c) kind)))
             (list 'fail 'raw-outside-unsafe (list name c))]
            [(and kind (not (same-obligations? (oracle-obligations kind)
                                               (ptr-sidecar-obligations sidecar kind))))
             (list 'fail 'obligation-mismatch
                   (list kind (oracle-obligations kind)
                         (ptr-sidecar-obligations sidecar kind)))]
            [(and (eq? name 'R-UnsafeExit) (contains-ptrval? (config-control next)))
             (list 'fail 'ptrval-escapes-unsafe (config-control next))]
            [(and (eq? name 'R-Yield) (yield-under-unsafe? c)
                  (for/or ([obs (in-list (trace-additions current next))])
                    (contains-ptrval? obs)))
             (list 'fail 'ptrval-in-observation (trace-additions current next))]
            [else
             (when kind (bump! counters kind))
             (when (eq? name 'R-UnsafeExit) (bump! counters 'unsafe-exit))
             (when (and (eq? name 'R-Yield) (yield-under-unsafe? c))
               (bump! counters 'yield-in-unsafe))
             (loop next (sub1 remaining))])])])))
