#lang racket

(require rackunit
         racket/list
         racket/match
         redex/reduction-semantics
         "../borrow-gen.rkt"
         "../borrow.rkt"
         "../gen.rkt"
         "../lang.rkt"
         "../machine.rkt"
         "../region.rkt"
         "../typing.rkt")

(define owner-type '(Record ((n Int imm) (owned (Owned Res) imm))))
(define borrowed-record-type
  '(Record ((b (Borrowed Int (RParam %omitted)) imm))))
(define function-type `(NFn (,owner-type) Int () (Own) () User))

(define (typed-body body result-type)
  (define core
    `(Lam User adopt-check (raw)
       (Handle (Return boundary ,result-type)
               (return-value -> return-value)
               (Scope ()
                 (Let (x let ,owner-type) raw ,body)))))
  (define ir (build-region-ir core))
  (type-of/raw (annotate-regions core ir)
               '()
               `((adopt-check (NFn (,owner-type) ,result-type () (Own) () User)))
               '()
               (region-ctx ir '() (hash) (hash))))

(define (typed-scoped-record-escape)
  (define core
    `(Scope (1)
       (Let (r let ,borrowed-record-type)
            (Scope (2)
              (Rec ((b imm (ProjBorrow (Borrow 2) n)))))
            r)))
  (define ir (build-region-ir core))
  (type-of/raw (annotate-regions core ir)
               (list (list 1 owner-type) (list 2 owner-type))
               '()
               '()
               (region-ctx ir '()
                           (hash 1 (region-at ir '())
                                 2 (region-at ir '(0 0)))
                           (hash))))

(define (result-key result)
  (match result
    [`(fail ,key ,_node ,_details ...) key]
    [_ #f]))

(define (result-type result)
  (match result
    [`(ok (,type ,_row)) type]
    [_ #f]))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [fuel 200])
    (when (zero? fuel) (error 'trace-g2 "fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() configs]
      [(list (list _ next)) (loop next (append configs (list next)) (sub1 fuel))]
      [steps (error 'trace-g2 "一意な次状態でない: ~s" steps)])))

(define (trace-and-check core expected)
  (match (prepare-borrow-term* core)
    [(list 'ok start _sidecar _ir actual)
     (define configs (trace-g2 start))
     (define rows
       (for/list ([config (in-list configs)])
         (runtime-row config '() expected)))
     (define first-live
       (for/first ([row (in-list rows)] [index (in-naturals)] #:when row) index))
     (check-equal? actual expected)
     (check-not-false first-live "trace に runtime-row がある")
     (for ([config (in-list (drop configs first-live))]
           [row (in-list (drop rows first-live))]
           [index (in-naturals first-live)])
       (check-not-false row (format "config ~a の runtime-row: ~s" index config))
       (check-true (config-ok? config '() expected row)
                   (format "config ~a の config-ok?: ~s" index config)))
     (check-true (redex-match? G2m v (match (last configs)
                                      [`(cfg ,value ,_ ...) value]))
                 "終端が値")]
    [other (fail (format "Core が型検査されなかった: ~s; typing=~s"
                         other (checked-core core)))]))

(define (checked-core core)
  (define ir (build-region-ir core))
  (type-of/raw*+borrows
   (annotate-regions (fill-region-placeholders core ir) ir)
   '() '() '() (region-ctx ir '() (hash) (hash))))

;; Surface の注釈付き／注釈なしはどちらも #:ty を持つ同じ Core 形になる。
(test-case "借用欄を持つ record let は推論寿命を採る"
  (define result
    (typed-body
     `(Let (r let ,borrowed-record-type)
           (Rec ((b imm (ProjBorrow (Borrow x) n))))
           (Read (Proj r b)))
     'Int))
  (check-false (result-key result) (format "typing result: ~s" result))
  (check-equal? (result-type result) function-type))

(define (local-borrowed-record field-name owner-name)
  `(Rec ((,field-name imm
          (ProjBorrow (Borrow ,owner-name) n)))))

(test-case "record 欄の表は借用欄だけに所有者を付ける"
  (define value '(Rec ((plain imm 42) (borrowed imm (Borrow 7)))))
  (define table (capability-field-table (empty-region-ctx) value))
  (check-equal? (car (hash-ref table (cons 'record-field 'plain))) (set))
  (check-equal? (car (hash-ref table (cons 'record-field 'borrowed))) (set '(7)))
  (check-equal? (borrow-token-key (empty-region-ctx) `(Proj ,value plain)) (set))
  (check-equal? (borrow-token-key (empty-region-ctx) `(Proj ,value borrowed))
                (set '(7)))
  (check-equal? (borrow-token-key (empty-region-ctx) `(Proj ,value missing)) (set))
  ;; 表の無い旧来の operand だけは、従来の aggregate capability を保つ。
  (check-equal? (borrow-token-key (empty-region-ctx) '(Proj (Borrow 7) borrowed))
                (set '(7))))

(test-case "record let の欄を読める trace は全 config が整合する"
  (trace-and-check
   '(Scope ()
      (Let (x let (Owned (Record ((n Int mut))))) (Rec ((n mut 1)))
        (Let (r let (Record ((b (Borrowed Int (RVar 0)) imm))))
             (Rec ((b imm (ProjBorrow (Borrow x) n))))
          (Read (Proj r b)))))
   'Int))

(test-case "異なる owner の借用欄は片方を読んでも両 owner を Move できない"
  (define (core moved)
    `(Scope ()
       (Let (x let (Owned (Record ((n Int mut))))) (Rec ((n mut 1)))
         (Let (y let (Owned (Record ((n Int mut))))) (Rec ((n mut 2)))
           (Let (r let (Record ((left (Borrowed Int (RVar 0)) imm)
                                (right (Borrowed Int (RVar 0)) imm))))
                (Rec ((left imm (ProjBorrow (Borrow x) n))
                     (right imm (ProjBorrow (Borrow y) n))))
             (Let (read const Int) (Read (Proj r left)) (Move ,moved)))))))
  (for ([owner '(x y)])
    (define result (checked-core (core owner)))
    (check-equal? (result-key result) 'move-borrowed
                  (format "owner=~a result=~s" owner result))))

(test-case "入れ子 record の二段 Proj で借用欄を読める"
  (define nested-type
    '(Record ((inner (Record ((b (Borrowed Int (RParam %omitted)) imm))) imm))))
  (define result
    (typed-body
     `(Let (r let ,nested-type)
           (Rec ((inner imm
                  (Rec ((b imm (ProjBorrow (Borrow x) n)))))))
           (Read (Proj (Proj r inner) b)))
     'Int))
  (check-false (result-key result) (format "typing result: ~s" result))
  (check-equal? (result-type result) function-type))

(test-case "入れ子 record の欄を読む trace は全 config が整合する"
  (trace-and-check
   '(Scope ()
      (Let (x let (Owned (Record ((n Int mut))))) (Rec ((n mut 1)))
        (Let (r let
                (Record ((inner (Record ((b (Borrowed Int (RVar 0)) imm))) imm))))
             (Rec ((inner imm
                    (Rec ((b imm
                           (ProjBorrow (Borrow x) n)))))))
          (Read (Proj (Proj r inner) b)))))
   'Int))

(test-case "ProjOpt は some の payload に欄 capability を包み Absent は空にする"
  (define Λ (empty-region-ctx))
  (define present '(Rec ((maybe imm (Borrow 7)))))
  (define projected `(ProjOpt (Borrowed Int (RVar 0)) ,present maybe))
  (define some-table (capability-field-table Λ projected))
  (check-equal? (car (hash-ref some-table (cons 'some 0))) (set '(7)))
  (define eliminated
    `(Eliminate ,projected ((none () -> 0) (some (value) -> (Reborrow value)))))
  (check-equal? (borrow-token-key Λ eliminated) (set '(7)))
  (define absent
    '(Rec ((maybe imm (Absent (Borrowed Int (RVar 0)))))))
  (define absent-projected
    `(ProjOpt (Borrowed Int (RVar 0)) ,absent maybe))
  (check-equal? (car (hash-ref (capability-field-table Λ absent-projected)
                               (cons 'some 0)))
                (set))
  (trace-and-check
   '(Scope ()
      (Let (x let (Owned (Record ((n Int mut))))) (Rec ((n mut 1)))
        (Let (r let (Record ((maybe (Borrowed Int (RVar 0)) imm))))
             (Rec ((maybe imm (ProjBorrow (Borrow x) n))))
          (Let (option let (Option (Borrowed Int (RVar 0))))
               (ProjOpt (Borrowed Int (RVar 0)) r maybe)
            (Eliminate option
              ((none () -> 0) (some (value) -> (Read value))))))))
   'Int))

(define (rewritten-borrow-record body)
  `(Scope ()
     (Let (x let (Owned (Record ((n Int mut))))) (Rec ((n mut 1)))
       (Let (r let (Record ((b (BorrowedMut Int (RVar 0)) imm))))
            (Rec ((b imm (ProjBorrow (BorrowMut x) n)) (number imm 1)))
         (Let (rewritten let
                         (Record ((b (BorrowedMut Int (RVar 0)) imm)
                                  (number Int imm))))
              (RecRewrite r
                ((number value Int imm Int ,body)))
           (Read (Proj rewritten b)))))))

(test-case "RecRewrite の書換え欄と借用の通過は trace の全 config で整合する"
  (trace-and-check (rewritten-borrow-record 2) 'Int))

(test-case "RecRewrite で書き換えた借用欄の表は入力欄でなく結果を使う"
  (define rewritten
    '(RecRewrite (Rec ((borrowed imm (Borrow 1)) (other imm (Borrow 2))))
       ((borrowed source (Borrowed Int (RVar 0)) imm
         (Borrowed Int (RVar 0)) (Borrow 3)))))
  (define table (capability-field-table (empty-region-ctx) rewritten))
  (check-equal? (car (hash-ref table (cons 'record-field 'borrowed))) (set '(3)))
  (check-equal? (car (hash-ref table (cons 'record-field 'other))) (set '(2))))

(define (merged-record-core producer owner-a owner-b)
  `(Scope ()
     (Let (x let (Owned (Record ((n Int mut))))) (Rec ((n mut 1)))
       (Let (y let (Owned (Record ((n Int mut))))) (Rec ((n mut 2)))
         (Let (r let (Record ((borrowed (Borrowed Int (RVar 0)) imm))))
              ,(producer owner-a owner-b)
           (Let (read const Int) (Read (Proj r borrowed)) unit))))))

(define (bool-record-branches left right)
  `(Eliminate (Construct Bool true)
     ((true () -> ,(local-borrowed-record 'borrowed left))
      (false () -> ,(local-borrowed-record 'borrowed right)))))

(define (union-record-branches left right)
  `(UnionEliminate (UnionInject (Union Bool Int) Bool (Construct Bool true))
     ((Bool tag -> ,(local-borrowed-record 'borrowed left))
      (Int tag -> ,(local-borrowed-record 'borrowed right)))))

(test-case "Eliminate と UnionEliminate の合流後も借用欄の trace が整合する"
  (trace-and-check (merged-record-core bool-record-branches 'x 'y) 'Unit)
  (trace-and-check (merged-record-core union-record-branches 'x 'y) 'Unit))

(test-case "合流した record の欄を読む間は両 owner の Move を拒否する"
  (for* ([producer (list bool-record-branches union-record-branches)]
         [owner '(x y)])
    (define core
      `(Scope ()
         (Let (x let (Owned (Record ((n Int mut))))) (Rec ((n mut 1)))
           (Let (y let (Owned (Record ((n Int mut))))) (Rec ((n mut 2)))
             (Let (r let (Record ((borrowed (Borrowed Int (RVar 0)) imm))))
                  ,(producer 'x 'y)
               (Let (read const Int) (Read (Proj r borrowed)) (Move ,owner)))))))
    (define result (checked-core core))
    (check-equal? (result-key result) 'move-borrowed
                  (format "owner=~a result=~s" owner result))))

(test-case "通常の注釈なし let の推論寿命採用を保つ"
  (define result
    (typed-body
     '(Let (r let (Borrowed Int (RParam %omitted)))
           (ProjBorrow (Borrow x) n)
           (Read r))
     'Int))
  (check-false (result-key result))
  (check-equal? (result-type result) function-type))

(test-case "所有者の Scope を越える借用欄付き record を拒否する"
  (define result (typed-scoped-record-escape))
  (check-equal? (result-key result) 'borrow-escapes-owner))
