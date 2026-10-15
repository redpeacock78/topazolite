#lang racket
(require rackunit "../classify.rkt" "../typing.rkt")

(define structural-callables
  '((list-loop-id (NFn ((List Int)) Int () () () User))))

(define (never-with-normal type name)
  `(Let (,name const ,type)
     (Perform (Return classify-boundary ,type)
              (Perform (Return classify-boundary Int) 1))
     ,name))

(define list-never (never-with-normal '(List Int) 'list-value))
(define union-list-type '(Union (List Int) String))
(define union-never (never-with-normal union-list-type 'union-value))
(define function-type '(NFn () Int () () () User))
(define function-never (never-with-normal function-type 'function-value))

; 分類器は実行時の型 Never ではなく、正常型から schema と callable row を読む。
(test-case "Never の schema と関数位置は正常型で分類する"
  (check-equal? (third (core-type-of/normal list-never '() structural-callables))
                '(List Int))
  (check-equal? (third (core-type-of/normal union-never '() structural-callables))
                union-list-type)
  (check-equal? (third (core-type-of/normal function-never '() '())) function-type)
  (check-equal?
   (classify `(Eliminate ,list-never
               ((nil () -> 0) (cons (head tail) -> 1))) '() '())
   '(Finite no-recursion))
  (check-equal?
   (classify `(UnionEliminate ,union-never
               (((List Int) items -> 1) (String text -> 2))) '() '())
   '(Finite no-recursion))
  (check-equal? (classify `(Apply ,function-never) '() '())
                '(Finite no-recursion)))

; bmode 付き Let（3 要素 binding）が再帰呼び出しを包んでも structural を保つ。
; walker の bmode Let 分岐が無いと (Let (r const Int) ...) が fallthrough し Unknown になる。
(define let-loop
  '(Recur list-loop-id loop (xs)
          (Eliminate xs
                     ((nil () -> 0)
                      (cons (head tail) ->
                            (Let (r const Int) (Apply loop tail) r))))
          (Apply loop (Construct (List Int) nil))))
(check-equal? (classify let-loop '() structural-callables) '(Finite structural))

; Rec は record リテラルであり productivity guard ではない（core-calculus.md §6.2）。
; よって Rec／Proj で再帰呼び出しを包んでも productivity は変わらず、構造再帰として (Finite structural)。
; walker に Rec／Proj／Absent の分岐が無いと fallthrough し Unknown へ誤分類する。
(define rec-loop
  '(Recur list-loop-id loop (xs)
          (Eliminate xs
                     ((nil () -> 0)
                      (cons (head tail) ->
                            (Proj (Rec ((r imm (Apply loop tail))
                                       (absent imm (Absent Int))))
                                  r))))
          (Apply loop (Construct (List Int) nil))))
(check-equal? (classify rec-loop '() structural-callables) '(Finite structural))

(define projopt-loop
  '(Recur list-loop-id loop (xs)
          (Eliminate xs
                     ((nil () -> 0)
                      (cons (head tail) ->
                            (Let (record const
                                         (Record ((a Int imm) (r Int imm opt))))
                                 (Rec ((a imm 0)
                                       (r imm (Apply loop tail))))
                              (Eliminate (ProjOpt Int record r)
                                         ((some (projected) -> projected)
                                          (none () -> 0)))))))
          (Apply loop (Construct (List Int) nil))))
(check-equal? (classify projopt-loop '() structural-callables)
              '(Finite structural))
