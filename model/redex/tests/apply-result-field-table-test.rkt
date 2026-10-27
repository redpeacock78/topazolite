#lang racket

(require rackunit
         racket/match
         "../borrow.rkt"
         "../diagnostic.rkt"
         "../region.rkt"
         "../typing.rkt")

(define (raw-result core callables)
  (define ir (build-region-ir core))
  (type-of/raw (annotate-regions core ir)
               '((1 Int)) callables '()
               (region-ctx ir '() (hash) (hash))))

(define (callable-summaries core callables)
  (define ir (build-region-ir core))
  (sixth (typing-inference (annotate-regions core ir)
                           '((1 Int)) callables '()
                           (region-ctx ir '() (hash) (hash)))))

(define (failure-key result)
  (match result
    [(list 'fail key _ _) key]
    [_ #f]))

(define (formal-callable name parameter-type return-type body effects)
  (define signature
    `(ForallRegion (a)
       (NFn (,parameter-type) ,return-type () ,effects () User)))
  (values
   `(Scope (1) (RegionLam (a) (Lam User ,name (x) ,body)))
   `((,name ,signature))))

(define shared-record
  '(Record ((inner (Borrowed Int (RParam a)) imm)
            (other (Borrowed Int (RParam a)) imm))))

(test-case "record 仮引数の borrowed field を Read できる"
  (define-values (core callables)
    (formal-callable 'read-inner shared-record 'Int '(Read (Proj x inner)) '()))
  (check-equal? (failure-key (raw-result core callables)) #f))

(test-case "兄弟の borrowed field は別の formal key を持つ"
  (define parameter-type
    '(Record ((inner (BorrowedMut Int (RParam a)) imm)
              (other (BorrowedMut Int (RParam a)) imm))))
  (define body
    '(Let (read let Int) (Read (Proj x inner))
       (Assign (Proj x other) 7)))
  (define-values (core callables)
    (formal-callable 'read-write-fields parameter-type 'Unit body '(Mutation)))
  (check-equal? (failure-key (raw-result core callables)) #f))

(test-case "formal field の Option binder と sibling field の書込みが共存する"
  (define parameter-type
    '(Record ((inner (Option (BorrowedMut Int (RParam a))) imm)
              (other (BorrowedMut Int (RParam a)) imm))))
  (define body
    '(Eliminate (Proj x inner)
       ((none () -> (Assign (Proj x other) 1))
        (some (c) ->
          (Let (updated let Unit) (Assign c 2)
            (Assign (Proj x other) 3))))))
  (define-values (core callables)
    (formal-callable 'write-option-field parameter-type 'Unit body '(Mutation)))
  (check-equal? (failure-key (raw-result core callables)) #f))

(test-case "Union 仮引数の payload formal key を枝 binder へ渡す"
  (define parameter-type
    '(Union (BorrowedMut Int (RParam a)) Int))
  (define body
    '(UnionEliminate x
       (((BorrowedMut Int (RParam a)) c -> (Read c))
        (Int n -> n))))
  (define-values (core callables)
    (formal-callable 'read-union-payload parameter-type 'Int body '()))
  (check-equal? (failure-key (raw-result core callables)) #f))

(test-case "形式が違う関数仮引数の既存 formal key はそのまま"
  (define core
    '(Scope (1)
       (RegionLam (a)
         (Lam User useb (x)
           (Let (t let Int) (Read x) (Assign x 7))))))
  (define callables
    '((useb (ForallRegion (a)
             (NFn ((BorrowedMut Int (RParam a))) Unit
                  () (Mutation) () User)))))
  (check-equal? (failure-key (raw-result core callables)) #f))

(test-case "formal leaf API は宣言寿命と実引数 source alpha を分ける"
  (define parameter-type
    '(Record ((inner (BorrowedMut Int (RParam a)) imm)
              (other (BorrowedMut Int (RParam b)) imm))))
  (define core
    '(Scope (1)
       (RegionLam (a b)
         (Lam User read-inner (x) (Read (Proj x inner))))))
  (define callables
    `((read-inner (ForallRegion (a b)
                    (NFn (,parameter-type) Int () () () User)))))
  (define summary (first (callable-summaries core callables)))
  (define-values (inner-lifetime inner-sources)
    (formal-leaf-info
     summary 0 '(inner)
     (capability-entry (set) (set) #f #f (set 'inner-source) #f)))
  (define-values (other-lifetime other-sources)
    (formal-leaf-info
     summary 0 '(other)
     (capability-entry (set) (set) #f #f (set 'other-source) #f)))
  (check-true (match inner-lifetime [(list 'RParam _) #t] [_ #f]))
  (check-true (match other-lifetime [(list 'RParam _) #t] [_ #f]))
  (check-not-equal? inner-lifetime other-lifetime)
  (check-equal? inner-sources (set 'inner-source))
  (check-equal? other-sources (set 'other-source)))

(test-case "Recur と RecurVal の frame に formal field の欄表を保つ"
  (define parameter-type
    '(Record ((inner (BorrowedMut Int (RParam a)) imm)
              (other (BorrowedMut Int (RParam b)) imm))))
  (define callables
    `((rec-formal (NFn (,parameter-type) Int () () () User))))
  (define recur-value
    '(Scope (1)
       (RegionLam (a b)
         (RecurVal rec-formal g (x) (Read (Proj x inner))))))
  (define summary (first (callable-summaries recur-value callables)))
  (define-values (lifetime sources)
    (formal-leaf-info
     summary 0 '(inner)
     (capability-entry (set) (set) #f #f (set 'recur-source) #f)))
  (check-true (match lifetime [(list 'RParam _) #t] [_ #f]))
  (check-equal? sources (set 'recur-source))
  (define recur
    '(Scope (1)
       (RegionLam (a b)
         (Recur rec-formal g (x) (Read (Proj x inner)) 0))))
  (check-equal? (failure-key (raw-result recur callables)) #f))
