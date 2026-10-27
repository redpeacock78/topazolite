#lang racket

(require rackunit
         racket/list
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
  (formal-callable/regions '(a) name parameter-type return-type body effects))

(define (formal-callable/regions regions name parameter-type return-type body effects)
  (define signature
    `(ForallRegion ,regions
       (NFn (,parameter-type) ,return-type () ,effects () User)))
  (values
   `(Scope (1) (RegionLam ,regions (Lam User ,name (x) ,body)))
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
          (Let (other-updated let Unit) (Assign (Proj x other) 3)
            (Assign c 2))))))
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

(test-case "formal leaf API は宣言寿命と渡された source alpha を分ける"
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
     summary 0 '((record-field . inner))
     (capability-entry (set) (set) #f #f (set 'inner-source) #f)))
  (define-values (other-lifetime other-sources)
    (formal-leaf-info
     summary 0 '((record-field . other))
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
     summary 0 '((record-field . inner))
     (capability-entry (set) (set) #f #f (set 'recur-source) #f)))
  (check-true (match lifetime [(list 'RParam _) #t] [_ #f]))
  (check-equal? sources (set 'recur-source))
  (define recur
    '(Scope (1)
       (RegionLam (a b)
         (Recur rec-formal g (x) (Read (Proj x inner)) 0))))
  (check-equal? (failure-key (raw-result recur callables)) #f))

(test-case "Union member と data constructor の formal path は region ごとに異なる"
  (define union-type
    '(Union (BorrowedMut Int (RParam a))
            (BorrowedMut Bool (RParam b))))
  (define-values (union-core union-callables)
    (formal-callable/regions '(a b) 'read-union union-type 'Int 0 '()))
  (define union-summary (first (callable-summaries union-core union-callables)))
  (define union-leaves (first (callable-summary-formal-fields union-summary)))
  (define-values (union-capability _union-metadata)
    (formal-capability-entry union-type 'formal-root))
  (check-true
   (set-member? (capability-entry-keys union-capability)
                '(formal-root Payload)))
  (define union-paths (hash-keys union-leaves))
  (check-equal? (length union-paths) 2)
  (define union-lifetimes
    (for/list ([path (in-list union-paths)])
      (define-values (lifetime _sources)
        (formal-leaf-info
         union-summary 0 path
         (capability-entry (set) (set) #f #f (set) #f)))
      (define declared
        (match (first path)
          [`(BorrowedMut ,_ ,region) region]
          [_ #f]))
      (check-equal? lifetime declared)
      lifetime))
  (check-equal? (length (remove-duplicates union-lifetimes equal?)) 2)
  (define result-type
    '(Result (BorrowedMut Int (RParam a))
             (BorrowedMut Bool (RParam b))))
  (define-values (result-core result-callables)
    (formal-callable/regions '(a b) 'read-result result-type 'Int 0 '()))
  (define result-summary (first (callable-summaries result-core result-callables)))
  (define-values (result-capability _result-metadata)
    (formal-capability-entry result-type 'formal-root))
  (check-true
   (set-member? (capability-entry-keys result-capability)
                '(formal-root 0)))
  (define result-paths '(((ok . 0)) ((ng . 0))))
  (define result-lifetimes
    (for/list ([path (in-list result-paths)])
      (define-values (lifetime _sources)
        (formal-leaf-info
         result-summary 0 path
         (capability-entry (set) (set) #f #f (set) #f)))
      lifetime))
  (check-equal? (length (remove-duplicates result-lifetimes equal?)) 2))

(test-case "同じ formal path の a,b,a 寿命衝突は曖昧のまま fail closed"
  (define-values (_entry leaves)
    (formal-capability-entry
     '(Record ((same (BorrowedMut Int (RParam a)) imm)
               (same (BorrowedMut Int (RParam b)) imm)
               (same (BorrowedMut Int (RParam a)) imm)))
     'formal-root))
  (check-false (hash-ref leaves '((record-field . same)) 'missing)))

(test-case "集約値の root は borrowed view ではなく leaf view はそのまま"
  (define-values (root leaves)
    (formal-capability-entry
     '(Record ((view (BorrowedMut Int (RParam a)) imm)))
     'formal-root))
  (check-false (capability-entry-borrowed-view? root))
  (check-true
   (capability-entry-borrowed-view?
    (hash-ref leaves '((record-field . view)))))
  (define-values (borrowed-root _borrowed-leaves)
    (formal-capability-entry '(BorrowedMut Int (RParam a)) 'formal-root))
  (check-true (capability-entry-borrowed-view? borrowed-root)))
