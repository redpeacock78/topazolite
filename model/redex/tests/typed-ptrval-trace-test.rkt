#lang racket

(require rackunit
         racket/list
         racket/match
         redex/reduction-semantics
         "../gen.rkt"
         "../lang.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../traits.rkt"
         "../typing.rkt"
         "../unsafe-gen.rkt")

(define rawptr-int
  '(RawPtr Int Mut NonNull (Align 1) (AddrSpace native) (Prov owned)))

(define pair-ledger
  (make-trait-ledger
   canonical-trait-env
   #:data '((Pair (A B) ((mkpair ((Param A) (Param B))))))
   #:fail (lambda args (error 'test "unexpected ledger failure: ~s" args))))

(define (prepared-config source)
  (match (prepare-unsafe-term source)
    [(list 'ok config _sidecar) config]
    [other (fail (format "source Core が型検査されなかった: ~s" other))]))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [rules '()] [fuel 100])
    (when (zero? fuel)
      (error 'trace-g2 "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() (values configs rules)]
      [(list (list rule next))
       (loop next (append configs (list next))
             (append rules (list rule)) (sub1 fuel))]
      [steps (error 'trace-g2 "一意な次状態を期待した: ~s" steps)])))

(define (config-core cfg)
  (match cfg [`(cfg ,core ,_ ...) core]))

(define (config-heap cfg)
  (match cfg [`(cfg ,_ ,heap ,_ ...) heap]))

(define (config-states cfg)
  (match cfg [`(cfg ,_ ,_ ,states ,_ ...) states]))

(define (config-type-failure-key cfg)
  (match cfg
    [`(cfg ,core ,heap ,states ,_tokens ,_trace)
     (define places
       (derive-places heap '() #:declared (config-declared-types cfg)))
     (define borrow-types
       (and places (recover-runtime-borrow-types core heap states places)))
     (and borrow-types
          (parameterize ([config-runtime-borrow-types borrow-types])
            (with-config-typing
             (lambda ()
               (match (type-of/raw core places '())
                 [`(fail ,key ,_node ,_details ...) key]
                 [_ #f])))))]
    [_ #f]))

(define (row-subset? left right)
  (term (row-⊆ ,left ,right)))

(define (borrow-allocation-pending? config)
  (match config
    [`(cfg ,core ,heap ,_states ,_tokens ,_trace)
     (or (and (null? heap) (contains-form? core 'Let))
         (and (or (contains-form? core 'BorrowAt)
                  (contains-form? core 'BorrowMutAt))
              (pair? heap)))]
    [_ #f]))

(define (check-config-trace configs expected)
  ;; c3n5 で回収する BorrowAt の place 確保前後だけを除き、以降を全て検査する。
  (define first-non-pending
    (for/first ([cfg (in-list configs)] [index (in-naturals)]
                #:unless (borrow-allocation-pending? cfg))
      index))
  (check-not-false first-non-pending "BorrowAt の setup 後に構成がある")
  (define skipped (if first-non-pending (take configs first-non-pending) '()))
  (check-true (andmap borrow-allocation-pending? skipped)
              "除外した prefix は BorrowAt の setup 構成だけである")
  (for ([cfg (in-list skipped)] [index (in-naturals)])
    (define row (runtime-row cfg '() expected))
    (check-not-false row
                     (format "除外 setup 構成 ~a の runtime-row がある" index))
    (check-true (and row (config-ok? cfg '() expected row))
                (format "除外 setup 構成 ~a が config-ok? を通る" index)))
  (define checked (if first-non-pending (drop configs first-non-pending) configs))
  (for ([cfg (in-list checked)] [index (in-naturals)])
    (check-false (borrow-allocation-pending? cfg)
                 (format "構成 ~a の後で BorrowAt 除外へ戻らない" index)))
  (check-false (ormap (lambda (cfg) (contains-form? cfg 'PtrVal)) skipped)
               "除外した BorrowAt setup prefix に PtrVal は含まれない")
  (define initial-row
    (and (pair? checked) (runtime-row (first checked) '() expected)))
  (check-not-false initial-row
                   (format "setup 後の構成は runtime-row を持つ: ~s"
                           (and (pair? checked) (first checked))))
  (for ([cfg (in-list checked)] [index (in-naturals)])
    (define row (runtime-row cfg '() expected))
    (check-not-false row (format "構成 ~a の runtime-row がある: ~s" index cfg))
    (when (and row initial-row)
      (check-true (row-subset? row initial-row)
                  (format "構成 ~a の row が起点を超えない" index)))
    (check-true (and row (config-ok? cfg '() expected row))
                (format "構成 ~a が config-ok? を通る: ~s" index cfg)))
  initial-row)

(define (find-node tree predicate)
  (cond
    [(predicate tree) tree]
    [(pair? tree)
     (or (find-node (car tree) predicate)
         (find-node (cdr tree) predicate))]
    [else #f]))

(define (contains-form? tree name)
  (and (find-node tree
                  (lambda (node)
                    (and (pair? node) (eq? (car node) name))))
       #t))

(define (replace-node tree predicate replacement)
  (cond
    [(predicate tree) replacement]
    [(pair? tree)
     (cons (replace-node (car tree) predicate replacement)
           (replace-node (cdr tree) predicate replacement))]
    [else tree]))

(define (check-stuck-mismatch source blocked-rule)
  (define-values (source-configs _source-rules)
    (trace-g2 (prepared-config source)))
  (define start
    (for/first ([cfg (in-list source-configs)]
                #:when
                (find-node (config-core cfg)
                           (lambda (node)
                             (match node
                               [`(AddressOf (BorrowMutRef ,_ ,_ ,_)) #t]
                               [_ #f]))))
      cfg))
  (check-not-false start "型検査済み source に AddressOf の実行構成がある")
  (define-values (configs rules) (trace-g2 start))
  (check-config-trace configs 'Int)
  (define terminal (last configs))
  (check-equal? (raw-steps-g2/named terminal) '() "guard で stuck になる")
  (check-false (memq blocked-rule rules) "型 guard の規則は発火しない")
  (define ptr
    (find-node (config-core terminal)
               (lambda (node)
                 (match node [`(PtrVal ,_ ,_ ,_) #t] [_ #f]))))
  (check-not-false ptr "stuck 構成に PtrVal が残る")
  (when ptr
    (match ptr
      [`(PtrVal ,place ,path (RawPtr Int ,_ ,_ ,_ ,_ ,_))
       (check-equal? (ptr-target-type (config-heap terminal) place path)
                     'Bool
                     "指す先は存在し、その型だけが埋め込み型と異なる")]
      [_ (fail (format "不一致 pointer の形が違う: ~s" ptr))])))

(test-case "AddressOf から RawLoad までの構成は型と row を保つ"
  (define start
    (prepared-config
     '(Scope ()
        (Let (x let (Owned Int)) 7
          (Unsafe (RawLoad (AddressOf (BorrowMut x))))))))
  (define-values (configs rules) (trace-g2 start))
  (check-equal? (last rules) 'R-ScopeValue)
  (check-not-false (memq 'R-AddressOf rules))
  (check-not-false (memq 'R-RawLoad rules))
  (check-config-trace configs 'Int))

(test-case "Moved owner への未使用 pointer は終端まで型と row を保つ"
  (define source
    `(Scope ()
       (Let (x let (Owned Int)) 7
         (Let (done let Unit)
              (Scope ()
                (Unsafe
                 (Let (p mut ,rawptr-int) (AddressOf (BorrowMut x)) unit)))
           (Drop (Move x))))))
  (define-values (configs rules) (trace-g2 (prepared-config source)))
  (check-not-false (memq 'R-Move rules))
  (check-equal? (raw-steps-g2/named (last configs)) '())
  (check-not-false
   (find-node (config-heap (last configs))
              (lambda (node) (match node [`(PtrVal ,_ ,_ ,_) #t] [_ #f])))
   "Move 後も未使用 PtrVal が heap に残る")
  (check-config-trace configs 'Unit))

(test-case "Moved owner への RawLoad は guard の位置で stuck する"
  (define source
    `(Scope ()
       (Let (x let (Owned Int)) 7
         (Let (done let Unit)
              (Scope ()
                (Unsafe
                 (Let (p mut ,rawptr-int) (AddressOf (BorrowMut x)) unit)))
           (Drop (Move x))))))
  (define-values (configs _rules) (trace-g2 (prepared-config source)))
  (check-config-trace configs 'Unit)
  (define pointer
    (find-node (config-heap (last configs))
               (lambda (node) (match node [`(PtrVal ,_ ,_ ,_) #t] [_ #f]))))
  (check-not-false pointer "終端 heap に Move 済み owner を指す PtrVal がある")
  (define stuck
    `(cfg (Unsafe (RawLoad ,pointer))
          ,(config-heap (last configs))
          ,(config-states (last configs))
          ,(match (last configs) [`(cfg ,_ ,_ ,_ ,tokens ,_) tokens])
          ,(match (last configs) [`(cfg ,_ ,_ ,_ ,_ ,events) events])))
  (check-config-trace (list stuck) 'Int)
  (check-equal? (raw-steps-g2/named stuck) '()
                "Moved owner への RawLoad は Available guard で stuck")
  (check-equal? (second (assoc (match pointer [`(PtrVal ,place ,_ ,_) place])
                                (config-states (last configs))))
                'Moved))

(test-case "PtrOffset 後の pointee 不一致は RawLoad と FromRawPtr の guard で止まる"
  (call-with-trait-ledger
   pair-ledger
   (lambda ()
     (define (source operation)
        `(Scope ()
          (Let (pair let (Owned (Data Pair (Int Bool))))
               (Construct (Data Pair (Int Bool)) mkpair
                          17 (Construct Bool true))
            (Eliminate (BorrowMut pair)
              ((mkpair (a b) -> (Unsafe ,operation)))))))
     (check-stuck-mismatch
      (source '(RawLoad (PtrOffset (AddressOf a) 1)))
      'R-RawLoad)
     (check-stuck-mismatch
      (source '(Read (FromRawPtr (PtrOffset (AddressOf a) 1) 0)))
      'R-FromRawPtrMut))))

(test-case "RawStore の trace は書込み前後で構成型付けを保つ"
  (define start
    (prepared-config
     '(Scope ()
        (Let (x let (Owned Int)) 7
          (Unsafe (RawStore (AddressOf (BorrowMut x)) 9))))))
  (define-values (configs rules) (trace-g2 start))
  (check-not-false (memq 'R-RawStore rules))
  (check-config-trace configs 'Unit))

(test-case "R-LetMutB の heap slot に格納した PtrVal を読み出して使う"
  (define source
    `(Scope ()
       (Let (x let (Owned Int)) 7
         (Unsafe
          (Let (p mut ,rawptr-int) (AddressOf (BorrowMut x))
            (RawLoad p))))))
  (define-values (configs rules) (trace-g2 (prepared-config source)))
  (check-not-false (memq 'R-LetMutB rules))
  (check-true
   (for/or ([cfg (in-list configs)])
     (contains-form? (config-heap cfg) 'PtrVal))
   "中間 heap に PtrVal が格納される")
  (check-not-false (memq 'R-RawLoad rules))
  (check-config-trace configs 'Int))

(test-case "手組み PtrVal と FromRawPtr を含む構成は型付けを保つ"
  (define ptr
    '(PtrVal 0 () (RawPtr Int Mut NonNull (Align 1)
                            (AddrSpace native) (Prov owned))))
  (define cfg
    `(cfg (Unsafe (Read (FromRawPtr ,ptr 0)))
          ((0 7 (declared (Owned Int))))
          ((0 Available)) () ()))
  (check-equal?
   (with-config-typing (lambda () (core-type-of ptr '((0 Int)) '())))
   (list rawptr-int '())
   "PtrVal 部分項は deriving-config? 下で埋め込み型を返す")
  (check-equal? (runtime-row cfg '() 'Int) '())
  (check-true
   (config-ok? cfg '() 'Int '())))

(test-case "PtrVal の構成検査は place と RawPtr の形を要求する"
  (define ptr
    '(PtrVal 9 () (RawPtr Int Mut NonNull (Align 1)
                            (AddrSpace native) (Prov owned))))
  (define core `(Unsafe (RawLoad ,ptr)))
  (define heap '((0 7 (declared (Owned Int)))))
  (define states '((0 Available)))
  (check-false (runtime-row `(cfg ,core ,heap ,states () ()) '() 'Int))
  (check-false (config-ok? `(cfg ,core ,heap ,states () ()) '() 'Int '(Unsafe)))
  (define malformed
    '(PtrVal 0 () (RawPtr Int Invalid NonNull (Align 1)
                            (AddrSpace native) (Prov owned))))
  (check-false
   (config-ok? `(cfg (Unsafe (RawLoad ,malformed)) ,heap ,states () ())
               '() 'Int '(Unsafe)))
  (define moved
    '(cfg (Unsafe (RawLoad (PtrVal 0 ()
                                   (RawPtr Int Mut NonNull (Align 1)
                                           (AddrSpace native) (Prov owned)))))
          ((0 7 (declared (Owned Int))))
          ((0 Moved)) () ()))
  (check-equal? (runtime-row moved '() 'Int) '())
  (check-true (config-ok? moved '() 'Int '())
              "Moved でも place が存在すれば構成型付けする")
  (check-equal? (core-type-of '(PtrVal 0 ()
                                       (RawPtr Int Mut NonNull (Align 1)
                                               (AddrSpace native) (Prov owned)))
                              '((0 Int)) '())
                'ill-typed))
