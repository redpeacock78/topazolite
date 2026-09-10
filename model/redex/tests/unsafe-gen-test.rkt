#lang racket

(require rackunit racket/match
         "../unsafe-gen.rkt"
         "../ptr-static.rkt")

;; unsafe.md §5.4。生成域の 5 つの形がすべて出る。
(test-case "生成域が 5 つの形をすべて出す（unsafe.md §5.4）"
  ;; 乱数は種を固定して再現させる。
  (random-seed 20260909)
  (define seen (make-hash))
  (define (mark! term)
    (let walk ([t term])
      (match t
        [`(RawLoad ,_) (hash-set! seen 'raw-load #t)]
        [`(RawStore ,_ ,_) (hash-set! seen 'raw-store #t)]
        [`(PtrOffset ,_ ,_) (hash-set! seen 'ptr-offset #t)]
        [`(FromRawPtr ,_ ,_) (hash-set! seen 'from-raw-ptr #t)]
        [`(Yield ,_ ,_) (hash-set! seen 'yield #t)]
        [_ (void)])
      (when (list? t) (for-each walk t))))
  (for ([_i (in-range 400)])
    (mark! (gen-unsafe-term 4)))
  (for ([k (in-list '(raw-load raw-store ptr-offset from-raw-ptr yield))])
    (check-true (hash-ref seen k #f) (format "~a が生成される" k))))

;; unsafe.md §5.4。型検査を通る項と落ちる項の双方が出る。
(test-case "受理と discard の双方が出る（unsafe.md §5.4）"
  ;; 乱数は種を固定して再現させる。
  (random-seed 20260909)
  (define accepted 0)
  (define discarded 0)
  (for ([_i (in-range 400)])
    (match (prepare-unsafe-term (gen-unsafe-term 4))
      [(list 'ok _config _sidecar) (set! accepted (add1 accepted))]
      ['discard (set! discarded (add1 discarded))]))
  (check-true (positive? accepted) "受理される項がある")
  (check-true (positive? discarded) "型検査で落ちる項がある"))

;; 条件 3 の回帰。Unsafe が RawPtr を返す形は生成域に含めるが、
;; 境界からの漏出を型検査が discard として止める。
(test-case "Unsafe が PtrVal を返す形は型検査で discard になる（unsafe.md §5.4）"
  (check-equal?
   (prepare-unsafe-term
    '(Scope ()
       (Let (x let (Owned Res)) (resource 1)
         (Unsafe (AddressOf (BorrowMut x))))))
   'discard))

;; unsafe.md §5.5。fp の末尾へ自然数の segment を積む唯一の経路。
(test-case "可変借用の Eliminate から作る pointer が型検査を通る（unsafe.md §5.4）"
  (define skeleton
    '(Scope ()
       (Let (z let (Owned (List Int)))
            (Construct (List Int) cons 1000
                       (Construct (List Int) nil))
            (Eliminate (BorrowMut z)
              ((cons (h t) ->
                     (Unsafe (RawLoad (PtrOffset (AddressOf h) 0))))
               (nil () -> 1000))))))
  (check-not-eq? (prepare-unsafe-term skeleton) 'discard))

;; FromRawPtr の ρ は生成項の節点自身の region から補われる。
(test-case "受理された FromRawPtr 形が sidecar に現れる（unsafe.md §5.4）"
  (match
      (prepare-unsafe-term
       '(Scope ()
          (Let (x let (Owned Res)) (resource 1)
            (Unsafe (Read (FromRawPtr (AddressOf (BorrowMut x)) 0))))))
    [(list 'ok _config sidecar)
     (check-true
      (for/or ([request (in-list (ptr-sidecar-requests sidecar))])
        (eq? (ptr-request-kind request) 'from-raw-ptr)))]
    [other
     (fail (format "FromRawPtr を含む項が受理されなかった: ~s" other))]))
