#lang racket

;; [REQ: BOR-005] 可変性を保つ join と、合流した field の射影。

(require rackunit
         racket/match
         "../region.rkt"
         "../borrow.rkt"
         "../span-core.rkt"
         "../type-equiv.rkt"
         "../typing.rkt")

(check-equal? (merge-field '(a Int imm) '(a Int imm opt)) '(a Int imm opt))
(check-equal? (merge-field '(a Int mut opt) '(a Int mut opt)) '(a Int mut opt))
(check-equal? (merge-field '(a Int mut) '(a Int mut)) '(a Int mut))

(define (run core ir τ_place)
  (type-of/raw (annotate-regions core ir)
               (list (list 1 τ_place)) '() '()
               (region-ctx ir '() (hash 1 (region-at ir '())) (hash))))

;; tag の無い異型 field からは mut Union field を作らない。
(check-false (merge-field '(a Int mut) '(a String mut)))

;; 単位 2。可変性が食い違う場合でも、tag の無い異型からは合流しない。
(check-false (merge-field '(a Int imm) '(a String mut)))

;; 単位 3。record 全体でも同じ結果になる。
(let-values ([(merged witnesses)
              (merge-record-types
               (list '(Record ((a Int mut)))
                     '(Record ((a String mut)))))])
  (check-false merged)
  (check-equal? witnesses '()))

;; Union の mut field 型。Eliminate の異型 mut 結果は上の枝再照合を通って
;; Let まで運ぶ。以下は同じ Union mut field 型に対する ProjBorrow/Assign
;; の規則を、合流経路とは独立に検査する。
(define LEFT '(Record ((p Int imm))))
(define RIGHT '(Record ((q Int imm))))
(define JOINED (normalize-type `(Union ,LEFT ,RIGHT)))
(define LEFT-VALUE `(UnionInject ,JOINED ,LEFT (Rec ((p imm 1)))))
(define RIGHT-VALUE `(UnionInject ,JOINED ,RIGHT (Rec ((q imm 2)))))

;; Eliminate の異型 mut field も、専用の枝再照合で実際の型付け経路へ届く。
(define merged-eliminate-core
  `(Let (b let (Record ((a ,JOINED mut))))
     (Eliminate
      (Construct Bool true)
      ((true () -> (Rec ((a mut ,LEFT-VALUE))))
       (false () -> (Rec ((a mut ,RIGHT-VALUE))))))
     b))
(check-equal? (core-type-of merged-eliminate-core '() '())
              `((Record ((a ,JOINED mut))) ()))

;; 部分 Union の枝も、枝側の全成分を合流 Union の成分へ照合する。
(define THIRD '(Record ((r Int imm))))
(define OUTER-JOINED
  (normalize-type `(Union ,(normalize-type `(Union ,LEFT ,RIGHT)) ,THIRD)))
(define THIRD-OUTER-VALUE
  `(UnionInject ,OUTER-JOINED ,THIRD (Rec ((r imm 3)))))
(define inner-merge-core
  `(Eliminate (Construct Bool true)
              ((true () -> (Rec ((a mut ,LEFT-VALUE))))
               (false () -> (Rec ((a mut ,RIGHT-VALUE)))))))
(define nested-merge-core
  `(Eliminate (Construct Bool true)
              ((true () -> ,inner-merge-core)
               (false () -> (Rec ((a mut ,THIRD-OUTER-VALUE)))))))
(check-equal? (core-type-of nested-merge-core '() '())
              `((Record ((a ,OUTER-JOINED mut))) ()))

;; imm field の枝再照合は従来の compat?（mut から imm への弱化）を使う。
(define imm-merge-core
  `(Let (b let (Record ((a ,JOINED imm))))
     (Eliminate (Construct Bool true)
       ((true () -> (Rec ((a imm ,LEFT-VALUE))))
        (false () -> (Rec ((a mut ,RIGHT-VALUE))))))
     b))
(check-equal? (core-type-of imm-merge-core '() '())
              `((Record ((a ,JOINED imm))) ()))

;; 経路 1。Union mut field を射影すると BorrowedMut になり、Assign へ渡せる。
;; Eliminate の合流そのものではなく、Union mut field の射影・代入規則を判別する。
(let ()
  (define core
    `(Assign (ProjBorrow (BorrowMut 1) a)
             ,LEFT-VALUE))
  (define ir (build-region-ir core))
  (define result (run core ir `(Record ((a ,JOINED mut)))))
  (check-equal? (first result) 'ok)
  (check-equal? (first (second result)) 'Unit))

;; 経路 2。片方の成分としか両立しない右辺は E-BOR-022 で落ちる（spec §9.2）。
;; 型は mut のままであり、書き込める値が無いだけである。
(let ()
  (define core
    '(Assign (ProjBorrow (BorrowMut 1) a)
             (Rec ((p imm 1)))))
  (define ir (build-region-ir core))
  (define result (run core ir `(Record ((a ,JOINED mut)))))
  (check-equal? (first result) 'fail)
  (check-equal? (second result) 'assign-union-variant))

;; 経路 3。Union mut field からの読み出しは Union を返す（spec §9.1）。
(let ()
  (define core '(Read (ProjBorrow (Borrow 1) a)))
  (define ir (build-region-ir core))
  (define result (run core ir `(Record ((a ,JOINED mut)))))
  (check-equal? (first result) 'ok)
  (check-equal? (first (second result)) JOINED))
