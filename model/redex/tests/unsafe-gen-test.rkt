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
