#lang racket

;; [REQ: BIT-002] 算術の写し先が Host の演算ではなく shim を指すことの検査。

(require racket/set
         rackunit
         redex/reduction-semantics
         "../backend-matrix.rkt"
         "../lang.rkt"
         "../lowering.rkt"
         "../pr-lang.rkt"
         "../pr-machine.rkt")

(define fuel 10000)

;; 源の primitive 値。origin は Reserved の 1 段で足りる。
(define (prim-value name)
  (term (PrimVal (Reserved ,(string->symbol (format "o-~a" name))) ,name)))

(define (lower-value-ok value)
  (define-values (status result) (lower-value value 'racket-cs))
  (check-eq? status 'ok (format "~s" result))
  result)

(define (lower-ok core)
  (define-values (status result) (lower core 'racket-cs))
  (check-eq? status 'ok (format "~s" result))
  result)

;; 目標項に現れる記号と数をすべて平らに並べる。
(define (atoms target)
  (cond
    [(null? target) '()]
    [(pair? target) (append (atoms (car target)) (atoms (cdr target)))]
    [else (list target)]))

;; 目標項に現れる PPrim の名前を、現れる順に並べる。
(define (prim-names target)
  (match target
    [`(PPrim ,name ,arguments ...)
     (cons name (append* (map prim-names arguments)))]
    [(? pair?) (append (prim-names (car target)) (prim-names (cdr target)))]
    [_ '()]))

;; 正典表の shim 列を読む。名前 1 つか #f である（backend-matrix.md §8.1）。
(define (row-shim-name feature-id)
  (fourth (assq feature-id backend-features)))

(test-case
 "every shim primitive lowers to an eta expanded shim call"
 ;; 引数個数は Γ0 から引くので、arity をここに写して二重定義にしない。
 (for ([name (in-list shim-primitives)])
   (define formals
     (for/list ([index (in-range 1 (add1 (primitive-arity name)))])
       (string->symbol (format "pa_~a" index))))
   (check-equal? (lower-value-ok (prim-value name))
                 `(PClosure () ,formals (PPrim ,(shim name) ,@formals))
                 (format "lowering of ~a" name))))

(test-case
 "the lowered term names no host operator and no source primitive name"
 ;; backend-matrix.md §9。禁じるのは生成物が Host の演算を直接指すことである。源の名前が
 ;; 符号化を経ずに残る経路も同じ検査で閉じる。
 (define forbidden '(+ - * < <= = add sub mul lt le eq acquire))
 (for ([name (in-list shim-primitives)])
   (define target (lower-value-ok (prim-value name)))
   (for ([atom (in-list (atoms target))])
     (check-false (memq atom forbidden)
                  (format "~a: ~s が写しに残っている" name atom)))
   (check-equal? (prim-names target) (list (shim name)))))

(test-case
 "the shim column of the table is exactly the image of shim"
 ;; 表と写しの二重定義を検査で閉じる。片方だけ直すと落ちる。
 (for ([name (in-list shim-primitives)])
   (check-equal? (row-shim-name (primitive-feature name)) (shim name)
                 (format "shim column of ~a" name)))
 ;; 頭シンボルの feature は shim を持たない。η 展開の closure を作るだけである。
 (check-false (row-shim-name 'primitive-value)))

(test-case
 "the target machine implements the table's shim names"
 (check-equal? (term (δpr ,(shim 'add) 2 3)) 5)
 (check-equal? (term (δpr ,(shim 'sub) 2 3)) -1)
 (check-equal? (term (δpr ,(shim 'mul) 2 3)) 6)
 (check-equal? (term (δpr ,(shim 'lt) 2 3)) (term (PTagged k:true)))
 (check-equal? (term (δpr ,(shim 'le) 3 3)) (term (PTagged k:true)))
 (check-equal? (term (δpr ,(shim 'eq) 3 4)) (term (PTagged k:false)))
 (check-equal? (term (δpr ,(shim 'acquire) 7)) (term (PResource 7))))

(test-case
 "the reserved rows name shims the Phase 0 machine does not implement"
 ;; backend-matrix.md §9。予約行は Phase 2 以降の feature である。実装済みに見えると、
 ;; 対応する型が無いまま意味論を書いたことになる。
 (for ([feature-id (in-list '(fixed-width-int bits-n))])
   (define name (row-shim-name feature-id))
   (check-equal? (term (δpr ,name 1)) (term undefined)
                 (format "~a at arity 1" name))
   (check-equal? (term (δpr ,name 1 2)) (term undefined)
                 (format "~a at arity 2" name))))

(test-case
 "closing the resource feature closes only the resource primitive"
 ;; 名前ごとの feature を写像の内側で引いていることの検査である。
 (define matrix
   (for/list ([row (in-list backend-features)])
     (if (eq? (first row) 'primitive-acquire)
         (list 'primitive-acquire 'unsupported 'unsupported (fourth row) #f
               "test seam")
         row)))
 (define-values (status target)
   (lower/with-matrix (prim-value 'add) 'racket-cs matrix))
 (check-eq? status 'ok (format "~s" target))
 (define-values (status/acquire diagnostic)
   (lower/with-matrix (prim-value 'acquire) 'racket-cs matrix))
 (check-eq? status/acquire 'capability)
 (check-eq? (capability-diagnostic-feature-id diagnostic) 'primitive-acquire))

(test-case
 "closing one arithmetic feature closes only that name"
 ;; backend-matrix.md §8.1。名前ごとに feature を持つので、add を閉じても他の 6 件は写せる。
 (define matrix
   (for/list ([row (in-list backend-features)])
     (if (eq? (first row) 'primitive-add)
         (list 'primitive-add 'unsupported 'unsupported (fourth row) #f
               "test seam")
         row)))
 (define-values (status diagnostic)
   (lower/with-matrix (prim-value 'add) 'racket-cs matrix))
 (check-eq? status 'capability)
 (check-eq? (capability-diagnostic-feature-id diagnostic) 'primitive-add)
 (for ([name (in-list shim-primitives)] #:unless (eq? name 'add))
   (define-values (status/other target)
     (lower/with-matrix (prim-value name) 'racket-cs matrix))
   (check-eq? status/other 'ok (format "~a: ~s" name target))))

(test-case
 "closing the head feature closes every primitive value"
 ;; 形の対応表が PrimVal に与える primitive-value は名前によらない層である。
 ;; これを閉じると 7 件すべての写しが閉じる。粗い側へ倒れるだけであり、部分的
 ;; な出力は返さない（backend-matrix.md §8.3、§8.4）。
 (define matrix
   (for/list ([row (in-list backend-features)])
     (if (eq? (first row) 'primitive-value)
         (list 'primitive-value 'unsupported 'unsupported #f #f "test seam")
         row)))
 (for ([name (in-list shim-primitives)])
   (define-values (status diagnostic)
     (lower/with-matrix (prim-value name) 'racket-cs matrix))
   (check-eq? status 'capability (format "~a" name))
   (check-eq? (capability-diagnostic-feature-id diagnostic)
              'primitive-value)))

(test-case
 "an arithmetic application runs through the shim to the same value"
 (define target (lower-ok (term (Apply ,(prim-value 'add) 2 3))))
 (check-equal? (prim-names target) (list (shim 'add)))
 (check-equal? (match (run-pr (inject-pr target) fuel)
                 ['timeout 'timeout]
                 [`(pcfg ,result ,_ ,_ ,_) result])
               5))
