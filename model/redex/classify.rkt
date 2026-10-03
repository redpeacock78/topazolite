#lang racket

(require racket/match
         racket/set
         "erase.rkt"
         "schema.rkt"
         "type-equiv.rkt"
         (only-in "type-shape.rkt" proj-borrow-mode)
         "typing.rkt")

(provide classify
         classify-recur-body
         type-equiv?
         strip-owned-prefix)

(define (lookup table key)
  (match (assoc key table)
    [(list _ value) value]
    [_ #f]))

;; §4.5。分類は region の束縛そのものを見ない。本体側の環境を作るときと、
;; 署名の仮引数を数えるときだけ 1 段剥がす。継続側は ForallRegion のまま
;; である。
(define (peel-forall-region type)
  (match type
    [`(ForallRegion (,_ ...) ,inner) inner]
    [_ type]))

(define (forall-region-params type)
  (match type
    [`(ForallRegion (,rps ...) ,_) rps]
    [_ '()]))

(define (owned-type? type)
  (match type
    [`(Owned ,_) #t]
    [_ #f]))

(define (extend environment names types)
  (append (map list names types) environment))

(define (callable-contexts callable function parameters
                           environment callables)
  (define signature (lookup callables callable))
  (match (and signature (peel-forall-region signature))
    [(and body-signature `(NFn ,parameter-types ,_ ,_ ,_ ,_ ,_))
     (and (= (length parameters) (length parameter-types))
          (let ([body-environment
                 (extend environment (list function) (list body-signature))]
                [function-environment
                 (extend environment (list function) (list signature))])
            (list
             ;; 本体は剥がした NFn、継続は元の署名を見る。
             (function-body-environment body-environment
                                        parameters parameter-types)
             function-environment)))]
    [_ #f]))

(define (lambda-environment callable parameters environment callables)
  (match (lookup callables callable)
    [`(NFn ,parameter-types ,_ ,_ ,_ ,_ ,_)
     (and (= (length parameters) (length parameter-types))
          (function-body-environment environment parameters parameter-types))]
    [_ #f]))

(define (branch-contexts scrutinee branches environment callables)
  (match (core-type-of scrutinee '() callables environment)
    [(list wrapper-type _)
     ;; 包みは data 型を包むだけで構成子を変えない。typing.rkt と同じ表を引き、
     ;; 剥がした型で schema を引いてから、欄の型を包み直す。
     (define-values (data-type rewrap)
       (peel-eliminate-wrapper wrapper-type))
     (define schema-core (constructor-schema data-type))
     (and schema-core
          (let* ([schema
                  (for/list ([row (in-list schema-core)])
                    (list (first row) (map rewrap (second row))))]
                 [contexts
                  (for/list ([branch (in-list branches)])
                   (match branch
                     [`(,constructor (,parameters ...) -> ,body)
                      (define field-types (lookup schema constructor))
                      (and field-types
                           (= (length parameters) (length field-types))
                           (list body
                                 (extend environment
                                         parameters field-types)
                                 parameters))]
                     [_ #f]))])
            (and (andmap identity contexts) contexts)))]
    [_ #f]))

(define (union-branch-contexts scrutinee branches environment callables)
  (match (core-type-of scrutinee '() callables environment)
    [(list source-type _)
     (define normalized (normalize-type source-type))
     (define-values (union-type rewrap)
       (match normalized
         [`(Union ,_ ,_) (values normalized values)]
         [`(Borrowed (Union ,_ ,_) ,rho)
          (values (second normalized)
                  (lambda (member) `(Borrowed ,member ,rho)))]
         [`(BorrowedMut (Union ,_ ,_) ,rho)
          (values (second normalized)
                  (lambda (member) `(BorrowedMut ,member ,rho)))]
         [_ (values #f #f)]))
     (and union-type
          (let* ([parsed
                  (for/list ([branch (in-list branches)])
                    (match branch
                      [`(,member ,binder -> ,body)
                       (list (normalize-type member) binder body)]
                      [_ #f]))]
                 [members (union-members union-type)])
            (and (andmap identity parsed)
                 (andmap (lambda (branch) (symbol? (second branch))) parsed)
                 (= (length parsed)
                    (length (remove-duplicates (map first parsed) type-equiv?)))
                 (for/and ([member (in-list members)])
                   (= (for/sum ([branch (in-list parsed)]
                                #:when (type-equiv? member (first branch)))
                        1)
                      1))
                 (for/list ([branch (in-list parsed)])
                   (define member (first branch))
                   (define binder (second branch))
                   (list (third branch)
                         (extend environment (list binder)
                                 (list (rewrap member)))
                         (list binder))))))]
    [_ #f]))

;; classify は Λ を持たない。callee の出口 row に必要な型だけを借用形から読み、
;; 対応できない形は #f にして Unknown 側へ倒す。
(define (borrow-free-type core environment)
  (define (recur inner) (borrow-free-type inner environment))
  (define (borrow-of place mode)
    (match (and (symbol? place) (lookup environment place))
      ;; region は row 判定に使わないため、型形を保つ仮値を置く。
      [`(Owned ,payload) `(,mode ,payload 0)]
      [_ #f]))
  (match core
    [(? symbol? name) (lookup environment name)]
    [`(Borrow ,place) (borrow-of place 'Borrowed)]
    [`(BorrowAt ,_ ,_ ,place) (borrow-of place 'Borrowed)]
    [`(BorrowMut ,place) (borrow-of place 'BorrowedMut)]
    [`(BorrowMutAt ,_ ,_ ,place) (borrow-of place 'BorrowedMut)]
    [`(Read ,inner)
     (match (let ([type (recur inner)]) (and type (normalize-type type)))
       [`(Borrowed ,payload ,_) payload]
       [`(BorrowedMut ,payload ,_) payload]
       [_ #f])]
    [`(Reborrow ,inner) (recur inner)]
    [`(ReborrowAt ,_ ,_ ,inner) (recur inner)]
    [`(ProjBorrow ,inner ,label) (project-borrow-type (recur inner) label)]
    [`(ProjBorrowAt ,_ ,_ ,inner ,label)
     (project-borrow-type (recur inner) label)]
    [_ #f]))

;; T-ProjBorrow と同じ規則で欄の借用型を作る。不正形と欠けた欄では #f。
(define (project-borrow-type type label)
  (define-values (parent-mode payload region)
    (match (and type (normalize-type type))
      [`(Borrowed ,payload ,region) (values 'Borrowed payload region)]
      [`(BorrowedMut ,payload ,region) (values 'BorrowedMut payload region)]
      [_ (values #f #f #f)]))
  (define field
    (match (and payload (normalize-type payload))
      [`(Record ,row) (assoc label row)]
      [_ #f]))
  (match field
    [(list _ field-type field-mode)
     (match (normalize-type field-type)
       [`(Owned ,_) #f]
       [_ `(,(proj-borrow-mode parent-mode field-mode) ,field-type ,region)])]
    [_ #f]))

(define (callee-type function environment callables)
  (match (core-type-of function '() callables environment)
    [(list type _) type]
    [_ (borrow-free-type function environment)]))

(define (latent-row-safe? function environment callables)
  (define (row-safe? latent-row)
    (not
     (ormap (lambda (label)
              (or (eq? label 'Partial)
                  (match label [`(Yield ,_) #t] [_ #f])))
            latent-row)))
  ;; §4.5。RegionApp は Λ 無しの core-type-of では region の実引数が
  ;; 生きておらず落ちる。頭の型だけを引き、ForallRegion を 1 段剥がす。
  (match function
    [`(RegionApp ,head (,_ ...))
     (match (callee-type head environment callables)
       [type
        (match (peel-forall-region type)
          [`(NFn ,_ ,_ ,_ ,latent-row ,_ ,_) (row-safe? latent-row)]
          [_ #f])])]
    [_
     (match (callee-type function environment callables)
       [`(NFn ,_ ,_ ,_ ,latent-row ,_ ,_) (row-safe? latent-row)]
       [_ #f])]))

(define (pre? target core environment callables)
  (define (walk core environment target-visible?)
    (match core
      [(or (? integer?) (? string?) 'unit (? symbol?)) #t]
      [`(Lam ,_ ,callable (,parameters ...) ,body)
       (define body-environment
         (lambda-environment callable parameters environment callables))
       (and body-environment
            (walk body body-environment
                  (and target-visible?
                       (not (memq target parameters)))))]
      [`(PrimVal ,_ ,_) #t]
      [`(CurryVal ,_ ,function ,argument)
       (and (walk function environment target-visible?)
            (walk argument environment target-visible?))]
      [`(RecurVal ,callable ,function (,parameters ...) ,body)
       (define contexts
         (callable-contexts callable function parameters
                            environment callables))
       (and contexts
            (walk body (first contexts)
                  (and target-visible?
                       (not (memq target
                                  (cons function parameters))))))]
      [`(TypeRep ,_ ,_ ,_) #t]
      [`(ProofRep ,_ ,_) #t]
      [`(UVal ,value) (walk value environment target-visible?)]
      [`(RVal ,_ ,value) (walk value environment target-visible?)]
      [`(BorrowRef ,_ ,_ ,_) #t]
      [`(BorrowMutRef ,_ ,_ ,_) #t]
      [`(PtrVal ,_ ,_ ,_ ,_) #t]
      [`(resource ,_) #t]
      [`(Absent ,_) #t]
      [`(Construct ,_ ,_ ,fields ...)
       (andmap (lambda (field)
                 (walk field environment target-visible?))
               fields)]
      [`(UnionInject ,_ ,_ ,payload)
       (walk payload environment target-visible?)]
      [`(Rec (,fields ...))
       (andmap (lambda (field)
                 (walk (third field) environment target-visible?))
               fields)]
      [`(Proj ,record ,_)
       (walk record environment target-visible?)]
      [`(ProjOpt ,_ ,record ,_)
       (walk record environment target-visible?)]
      [`(Apply ,function ,arguments ...)
       (define head
         (match function
           [`(RegionApp ,g (,_ ...)) g]
           [_ function]))
       (and (or (and target-visible?
                     (eq? head target))
                (latent-row-safe? function environment callables))
            (walk function environment target-visible?)
            (andmap (lambda (argument)
                      (walk argument environment target-visible?))
                    arguments))]
      [`(Let (,name ,type) ,bound ,body)
       (and (walk bound environment target-visible?)
            (walk body
                  (extend environment (list name)
                          (list type))
                  (and target-visible? (not (eq? name target)))))]
      [`(Let (,name ,_ ,type) ,bound ,body)
       (and (walk bound environment target-visible?)
            (walk body
                  (extend environment (list name)
                          (list type))
                  (and target-visible? (not (eq? name target)))))]
      [`(Eliminate ,scrutinee (,branches ...))
       (define contexts
         (branch-contexts scrutinee branches environment callables))
       (and contexts
            (walk scrutinee environment target-visible?)
            (for/and ([context (in-list contexts)])
              (walk (first context) (second context)
                    (and target-visible?
                         (not (memq target (third context)))))))]
      [`(UnionEliminate ,scrutinee (,branches ...))
       (define contexts
         (union-branch-contexts scrutinee branches environment callables))
       (and contexts
            (walk scrutinee environment target-visible?)
            (for/and ([context (in-list contexts)])
              (walk (first context) (second context)
                    (and target-visible?
                         (not (memq target (third context)))))))]
      [`(Perform ,_ ,argument)
       (walk argument environment target-visible?)]
      [`(Handle (Return ,_ ,type) (,name -> ,handler) ,body)
       (and (walk handler
                  (extend environment (list name) (list type))
                  (and target-visible? (not (eq? name target))))
            (walk body environment target-visible?))]
      [`(Scope ,_ ,body)
       (walk body environment target-visible?)]
      [`(OwnLeaf ,body)
       (walk body environment target-visible?)]
      [`(Discharge ,_ ,body)
       (walk body environment target-visible?)]
      [`(Recur ,callable ,function (,parameters ...) ,body ,continuation)
       (define contexts
         (callable-contexts callable function parameters
                            environment callables))
       (and contexts
            (walk body (first contexts)
                  (and target-visible?
                       (not (memq target
                                  (cons function parameters)))))
            (walk continuation (second contexts)
                  (and target-visible?
                       (not (eq? target function)))))]
      [`(Yield ,observed ,next)
       (and (walk observed environment target-visible?)
            (walk next environment target-visible?))]
      [`(Suspend ,body) (walk body environment target-visible?)]
      [`(Move ,_) #t]
      [`(Borrow ,_) #t]
      [`(BorrowMut ,_) #t]
      [`(BorrowAt ,_ ,_ ,_) #t]
      [`(BorrowMutAt ,_ ,_ ,_) #t]
      [`(MutSlot ,_) #t]
      [`(Assign ,place ,value)
       (and (walk place environment target-visible?)
            (walk value environment target-visible?))]
      [`(Reassign ,_ ,value)
       (walk value environment target-visible?)]
      [`(Read ,argument)
       (walk argument environment target-visible?)]
      [`(Reborrow ,argument)
       (walk argument environment target-visible?)]
      [`(ReborrowAt ,_ ,_ ,argument)
       (walk argument environment target-visible?)]
      [`(ProjBorrow ,argument ,_)
       (walk argument environment target-visible?)]
      [`(ProjBorrowAt ,_ ,_ ,argument ,_)
       (walk argument environment target-visible?)]
      [`(AddressOf ,argument)
       (walk argument environment target-visible?)]
      [`(PtrOffset ,pointer ,offset)
       (and (walk pointer environment target-visible?)
            (walk offset environment target-visible?))]
      [`(RawLoad ,pointer)
       (walk pointer environment target-visible?)]
      [`(RawStore ,pointer ,value)
       (and (walk pointer environment target-visible?)
            (walk value environment target-visible?))]
      [`(FromRawPtr ,pointer ,_)
       (walk pointer environment target-visible?)]
      [`(Unsafe ,body)
       (walk body environment target-visible?)]
      [`(Drop ,argument) (walk argument environment target-visible?)]
      [`(Curry ,function ,argument)
       (and (walk function environment target-visible?)
            (walk argument environment target-visible?))]
      [`(Error ,_) #t]
      [`(RegionLam (,_ ...) ,body)
       (walk body environment target-visible?)]
      [`(RegionApp ,f (,_ ...))
       (walk f environment target-visible?)]
      [_ #f]))
  (walk core environment #t))

(struct uses (seen? direct? calls) #:transparent)

(define no-uses (uses #f #t '()))

(define (combine-uses analyses)
  (uses (ormap uses-seen? analyses)
        (andmap uses-direct? analyses)
        (append-map uses-calls analyses)))

(define (target-uses target core [target-visible? #t])
  (define (walk core target-visible?)
    (match core
      [(or (? integer?) (? string?) 'unit) no-uses]
      [(? symbol? name)
       (if (and target-visible? (eq? name target))
           (uses #t #f '())
           no-uses)]
      [`(Lam ,_ ,_ (,parameters ...) ,body)
       (walk body (and target-visible? (not (memq target parameters))))]
      [`(PrimVal ,_ ,_) no-uses]
      [`(CurryVal ,_ ,function ,argument)
       (combine-uses (list (walk function target-visible?)
                           (walk argument target-visible?)))]
      [`(RecurVal ,_ ,function (,parameters ...) ,body)
       (walk body
             (and target-visible?
                  (not (memq target (cons function parameters)))))]
      [`(TypeRep ,_ ,_ ,_) no-uses]
      [`(ProofRep ,_ ,_) no-uses]
      [`(UVal ,value) (walk value target-visible?)]
      [`(RVal ,_ ,value) (walk value target-visible?)]
      [`(BorrowRef ,_ ,_ ,_) no-uses]
      [`(BorrowMutRef ,_ ,_ ,_) no-uses]
      [`(PtrVal ,_ ,_ ,_ ,_) no-uses]
      [`(resource ,_) no-uses]
      [`(Absent ,_) no-uses]
      [`(Construct ,_ ,_ ,fields ...)
       (combine-uses
        (map (lambda (field) (walk field target-visible?)) fields))]
      [`(UnionInject ,_ ,_ ,payload) (walk payload target-visible?)]
      [`(Rec (,fields ...))
       (combine-uses
        (map (lambda (field)
               (walk (third field) target-visible?))
             fields))]
      [`(Proj ,record ,_)
       (walk record target-visible?)]
      [`(ProjOpt ,_ ,record ,_)
       (walk record target-visible?)]
      [`(Apply ,function ,arguments ...)
       (define head
         (match function
           [`(RegionApp ,g (,_ ...)) g]
           [_ function]))
       (cond
         [(and target-visible? (eq? head target))
          (define children
            (combine-uses
             (map (lambda (argument) (walk argument target-visible?))
                  arguments)))
          (uses #t (uses-direct? children)
                (cons arguments (uses-calls children)))]
         [else
          (combine-uses
           (map (lambda (term) (walk term target-visible?))
                (cons function arguments)))])]
      [`(Let (,name ,_) ,bound ,body)
       (combine-uses
        (list (walk bound target-visible?)
              (walk body
                    (and target-visible? (not (eq? name target))))))]
      [`(Let (,name ,_ ,_) ,bound ,body)
       (combine-uses
        (list (walk bound target-visible?)
              (walk body
                    (and target-visible? (not (eq? name target))))))]
      [`(Eliminate ,scrutinee (,branches ...))
       (combine-uses
        (cons
         (walk scrutinee target-visible?)
         (for/list ([branch (in-list branches)])
           (match branch
             [`(,_ (,parameters ...) -> ,body)
              (walk body
                    (and target-visible?
                         (not (memq target parameters))))]
             [_ (uses #f #f '())]))))]
      [`(UnionEliminate ,scrutinee (,branches ...))
       (combine-uses
        (cons
         (walk scrutinee target-visible?)
         (for/list ([branch (in-list branches)])
           (match branch
             [`(,_ ,binder -> ,body)
              (walk body
                    (and target-visible? (not (eq? target binder))))]
             [_ (uses #f #f '())]))))]
      [`(Perform ,_ ,argument) (walk argument target-visible?)]
      [`(Handle ,_ (,name -> ,handler) ,body)
       (combine-uses
        (list (walk handler
                    (and target-visible? (not (eq? name target))))
              (walk body target-visible?)))]
      [`(Scope ,_ ,body) (walk body target-visible?)]
      [`(OwnLeaf ,body) (walk body target-visible?)]
      [`(Discharge ,_ ,body) (walk body target-visible?)]
      [`(Recur ,_ ,function (,parameters ...) ,body ,continuation)
       (combine-uses
        (list
         (walk body
               (and target-visible?
                    (not (memq target (cons function parameters)))))
         (walk continuation
               (and target-visible? (not (eq? target function))))))]
      [`(Yield ,observed ,next)
       (combine-uses (list (walk observed target-visible?)
                           (walk next target-visible?)))]
      [`(Suspend ,body) (walk body target-visible?)]
      [`(Move ,name) (walk name target-visible?)]
      [`(Borrow ,place) (walk place target-visible?)]
      [`(BorrowMut ,place) (walk place target-visible?)]
      [`(BorrowAt ,_ ,_ ,place) (walk place target-visible?)]
      [`(BorrowMutAt ,_ ,_ ,place) (walk place target-visible?)]
      [`(MutSlot ,_) no-uses]
      [`(Assign ,place ,value)
       (combine-uses (list (walk place target-visible?)
                           (walk value target-visible?)))]
      [`(Reassign ,place ,value)
       (combine-uses (list (walk place target-visible?)
                           (walk value target-visible?)))]
      [`(Read ,argument) (walk argument target-visible?)]
      [`(Reborrow ,argument) (walk argument target-visible?)]
      [`(ReborrowAt ,_ ,_ ,argument) (walk argument target-visible?)]
      [`(ProjBorrow ,argument ,_) (walk argument target-visible?)]
      [`(ProjBorrowAt ,_ ,_ ,argument ,_) (walk argument target-visible?)]
      [`(AddressOf ,argument) (walk argument target-visible?)]
      [`(PtrOffset ,pointer ,offset)
       (combine-uses (list (walk pointer target-visible?)
                           (walk offset target-visible?)))]
      [`(RawLoad ,pointer) (walk pointer target-visible?)]
      [`(RawStore ,pointer ,value)
       (combine-uses (list (walk pointer target-visible?)
                           (walk value target-visible?)))]
      [`(FromRawPtr ,pointer ,_) (walk pointer target-visible?)]
      [`(Unsafe ,body) (walk body target-visible?)]
      [`(Drop ,argument) (walk argument target-visible?)]
      [`(Curry ,function ,argument)
       (combine-uses (list (walk function target-visible?)
                           (walk argument target-visible?)))]
      [`(Error ,_) no-uses]
      [`(RegionLam (,_ ...) ,body)
       (walk body target-visible?)]
      [`(RegionApp ,f (,_ ...))
       (walk f target-visible?)]
      [_ (uses #f #f '())]))
  (walk core target-visible?))

(define (decreases-at? target parameters position body)
  (define root (list-ref parameters position))
  (define (remove-bound names variables)
    (for/fold ([remaining variables])
              ([name (in-list names)])
      (set-remove remaining name)))
  ;; 走査対象の位置にある Move は構造を保つ透過操作であり、根を辿る。
  ;; これは束縛別名の規則とは別で、Move を bound にした名前は rebind で継承しない。
  (define (transparent-root core)
    (match core
      [`(Move ,inner) (transparent-root inner)]
      [`(UnionInject ,_ ,_ ,inner) (transparent-root inner)]
      [_ core]))
  ;; Let の binder は外側の名前を落とすが、束縛する項がその名前そのものなら
  ;; 別名であり、根の資格をそのまま引き継ぐ。落としてから引き継ぎ直す。
  (define (rebind name bound decomposable strict)
    (define alias (and (symbol? bound) bound))
    (define kept-decomposable?
      (and alias (set-member? decomposable alias)))
    (define kept-strict?
      (and alias (set-member? strict alias)))
    (define next-decomposable (set-remove decomposable name))
    (define next-strict (set-remove strict name))
    (values (if kept-decomposable? (set-add next-decomposable name) next-decomposable)
            (if kept-strict? (set-add next-strict name) next-strict)))
  (define (walk core decomposable strict target-visible?)
    (match core
      [(or (? integer?) (? string?) 'unit (? symbol?)) #t]
      [`(Lam ,_ ,_ (,bound ...) ,body)
       (walk body
             (remove-bound bound decomposable)
             (remove-bound bound strict)
             (and target-visible? (not (memq target bound))))]
      [`(PrimVal ,_ ,_) #t]
      [`(CurryVal ,_ ,function ,argument)
       (and (walk function decomposable strict target-visible?)
            (walk argument decomposable strict target-visible?))]
      [`(RecurVal ,_ ,function (,bound ...) ,body)
       (define names (cons function bound))
       (walk body
             (remove-bound names decomposable)
             (remove-bound names strict)
             (and target-visible? (not (memq target names))))]
      [`(TypeRep ,_ ,_ ,_) #t]
      [`(ProofRep ,_ ,_) #t]
      [`(resource ,_) #t]
      [`(Absent ,_) #t]
      [`(Construct ,_ ,_ ,fields ...)
       (andmap (lambda (field)
                 (walk field decomposable strict target-visible?))
               fields)]
      [`(UnionInject ,_ ,_ ,payload)
       (walk payload decomposable strict target-visible?)]
      [`(Rec (,fields ...))
       (andmap (lambda (field)
                 (walk (third field)
                       decomposable strict target-visible?))
               fields)]
      [`(Proj ,record ,_)
       (walk record decomposable strict target-visible?)]
      [`(ProjOpt ,_ ,record ,_)
       (walk record decomposable strict target-visible?)]
      [`(Apply ,function ,arguments ...)
       (define head
         (match function
           [`(RegionApp ,g (,_ ...)) g]
           [_ function]))
       (and
        (if (and target-visible? (eq? head target))
            (and (= (length arguments) (length parameters))
                 (let ([argument (transparent-root (list-ref arguments position))])
                   (and (symbol? argument) (set-member? strict argument))))
            (walk function decomposable strict target-visible?))
        (andmap (lambda (argument)
                  (walk argument decomposable strict target-visible?))
                arguments))]
      [`(Let (,name ,_) ,bound ,body)
       (define-values (next-decomposable next-strict)
         (rebind name bound decomposable strict))
       (and (walk bound decomposable strict target-visible?)
            (walk body next-decomposable next-strict
                  (and target-visible? (not (eq? name target)))))]
      [`(Let (,name ,_ ,_) ,bound ,body)
       (define-values (next-decomposable next-strict)
         (rebind name bound decomposable strict))
       (and (walk bound decomposable strict target-visible?)
            (walk body next-decomposable next-strict
                  (and target-visible? (not (eq? name target)))))]
      [`(Eliminate ,scrutinee (,branches ...))
       (define root-of-scrutinee (transparent-root scrutinee))
       (define decomposed?
         (and (symbol? root-of-scrutinee)
              (set-member? decomposable root-of-scrutinee)))
       (and
        (walk scrutinee decomposable strict target-visible?)
        (for/and ([branch (in-list branches)])
          (match branch
            [`(,_ (,bound ...) -> ,branch-body)
             (define branch-decomposable
               (remove-bound bound decomposable))
             (define branch-strict (remove-bound bound strict))
             (walk branch-body
                   (if decomposed?
                       (for/fold ([result branch-decomposable])
                                 ([name (in-list bound)])
                         (set-add result name))
                       branch-decomposable)
                   (if decomposed?
                       (for/fold ([result branch-strict])
                                 ([name (in-list bound)])
                         (set-add result name))
                       branch-strict)
                   (and target-visible? (not (memq target bound))))]
            [_ #f])))]
      [`(UnionEliminate ,scrutinee (,branches ...))
       (define root-of-scrutinee (transparent-root scrutinee))
       (and
        (walk scrutinee decomposable strict target-visible?)
        (for/and ([branch (in-list branches)])
          (match branch
            [`(,_ ,bound -> ,branch-body)
             (define-values (branch-decomposable branch-strict)
               (rebind bound root-of-scrutinee decomposable strict))
             (walk branch-body
                   branch-decomposable
                   branch-strict
                   (and target-visible? (not (eq? target bound))))]
            [_ #f])))]
      [`(Perform ,_ ,argument)
       (walk argument decomposable strict target-visible?)]
      [`(Handle ,_ (,name -> ,handler) ,handled)
       (and (walk handler
                  (set-remove decomposable name)
                  (set-remove strict name)
                  (and target-visible? (not (eq? name target))))
            (walk handled decomposable strict target-visible?))]
      [`(Scope ,_ ,scoped)
       (walk scoped decomposable strict target-visible?)]
      [`(Recur ,_ ,function (,bound ...) ,nested-body ,continuation)
       (define body-bound (cons function bound))
       (and
        (walk nested-body
              (remove-bound body-bound decomposable)
              (remove-bound body-bound strict)
              (and target-visible? (not (memq target body-bound))))
        (walk continuation
              (set-remove decomposable function)
              (set-remove strict function)
              (and target-visible? (not (eq? target function)))))]
      [`(Yield ,observed ,next)
       (and (walk observed decomposable strict target-visible?)
            (walk next decomposable strict target-visible?))]
      [`(Suspend ,suspended)
       (walk suspended decomposable strict target-visible?)]
      [`(Move ,_) #t]
      [`(Drop ,argument)
       (walk argument decomposable strict target-visible?)]
      [`(Curry ,function ,argument)
       (and (walk function decomposable strict target-visible?)
            (walk argument decomposable strict target-visible?))]
      [`(Error ,_) #t]
      [`(RegionLam (,_ ...) ,body)
       (walk body decomposable strict target-visible?)]
      [`(RegionApp ,f (,_ ...))
       (walk f decomposable strict target-visible?)]
      [_ #f]))
  (walk body (set root) (set) #t))

(define (no-recursion? core)
  (cond
    [(not (list? core)) #t]
    [(null? core) #t]
    [(memq (car core) '(Recur RecurVal)) #f]
    [else (andmap no-recursion? core)]))

(define no-target (list 'no-target))

(define (no-self-reference? core environment callables)
  (match core
    [`(Recur ,callable ,function (,parameters ...) ,body ,continuation)
     (define contexts
       (callable-contexts callable function parameters
                          environment callables))
     (and contexts
          (not (uses-seen? (target-uses function body)))
          (pre? function body (first contexts) callables)
          (pre? function continuation (second contexts) callables))]
    [_ #f]))

(define (structural-body? function parameters body environment callables)
  (and (pre? function body environment callables)
       (let ([body-uses (target-uses function body)])
         (and (uses-direct? body-uses)
              (andmap (lambda (arguments)
                        (= (length arguments) (length parameters)))
                      (uses-calls body-uses))
              (for/or ([position (in-range (length parameters))])
                (decreases-at? function parameters position body))))))

(define (structural? core environment callables)
  (match core
    [`(Recur ,callable ,function (,parameters ...) ,body ,continuation)
     (define contexts
       (callable-contexts callable function parameters
                          environment callables))
     (and contexts
          (structural-body? function parameters body
                            (first contexts) callables)
          (pre? function continuation (second contexts) callables)
          (let ([continuation-uses (target-uses function continuation)])
            (and (uses-direct? continuation-uses)
                 (andmap (lambda (arguments)
                           (= (length arguments) (length parameters)))
                         (uses-calls continuation-uses)))))]
    [_ #f]))

(define (dangerous-guard-row? row)
  (ormap (lambda (label)
           (or (eq? label 'Own)
               (match label [`(Return ,_ ,_) #t] [_ #f])))
         row))

(define (yield-types row)
  (for/list ([label (in-list row)]
             #:when (match label [`(Yield ,_) #t] [_ #f]))
    (second label)))

(define (guard-component-row core environment callables expected-types)
  (match (core-type-of core '() callables environment)
    [(list _ row) row]
    [_
     (for/or ([expected (in-list expected-types)])
       (core-check-row core '() callables expected environment))]))

(define (guard-component? target core environment callables
                          [expected-types '()])
  (define analysis (target-uses target core))
  (and (not (uses-seen? analysis))
       (pre? target core environment callables)
       (let ([row
              (guard-component-row core environment callables
                                   expected-types)])
         (and row (not (dangerous-guard-row? row))))))

;; G5c5b1 spec §6.4。Owned の仮引数を持つ Recur の本体から、生成した Scope と
;; Let の連なりを外す。返り値は外した本体と、その本体を見るための環境の
;; 2 つ組である。契約を 1 つでも満たさなければ #f を返す。
;;
;; 外す個数は署名から決める。形を推測して受かるまで剥がすことはしない。
;; Scope の place 列と Let の宣言型と右辺まで見るのは、手で書いた不正な
;; Typed Core をここで受けないためである。
;;
;; ここは classify の内側であり、入口で erase-core した Core だけを見る。
;;
;; guarded-body? 自身は変えない。現在の生成は Eliminate の枝の先に Scope が
;; 現れる形を作らないためである。Scope を Eliminate の枝の内側へ置く生成を
;; 将来入れるときは、この判断を見直す必要がある。
(define (strip-owned-prefix callable parameters body environment callables)
  (match (peel-forall-region (lookup callables callable))
    [`(NFn ,parameter-types ,_ ,_ ,_ ,_ ,_)
     (cond
       [(not (= (length parameters) (length parameter-types))) #f]
       [else
        (define owned-positions
          (for/list ([name (in-list parameters)]
                     [type (in-list parameter-types)]
                     #:when (owned-type? type))
            (list name type)))
        (cond
          [(null? owned-positions) (list body environment)]
          [else
           (match body
             [`(Scope () ,inner)
              (let loop ([pending owned-positions]
                         [core inner]
                         [env environment])
                (cond
                  [(null? pending)
                   ;; 契約を満たす Let がもう 1 段続く形は受け付けない。
                   ;; 外す個数は署名が決めるためである。
                   (if (generated-owned-let? core parameters parameter-types)
                       #f
                       (list core env))]
                  [else
                   (match-define (list raw declared) (first pending))
                   (match core
                     [`(Let (,binder ,_ ,type) ,(? symbol? bound) ,next)
                      (and (eq? bound raw)
                           (type-equiv? type declared)
                           (loop (cdr pending)
                                 next
                                 (extend env (list binder) (list declared))))]
                     [_ #f])]))]
             [_ #f])])])]
    [_ #f]))

;; 連なりの内側に、生成した Let と見分けの付かない Let が続くかを見る。
(define (generated-owned-let? core parameters parameter-types)
  (match core
    [`(Let (,_ ,_ ,type) ,(? symbol? bound) ,_)
     (for/or ([name (in-list parameters)]
              [declared (in-list parameter-types)])
       (and (owned-type? declared)
            (eq? bound name)
            (type-equiv? type declared)))]
    [_ #f]))

(define (guarded-body? target parameter-types observed-types
                       core environment callables)
  (match core
    [`(Yield ,observed (Apply ,function ,arguments ...))
     (and (eq? function target)
          (= (length arguments) (length parameter-types))
          (guard-component? target observed environment callables
                            observed-types)
          (for/and ([argument (in-list arguments)]
                    [expected (in-list parameter-types)])
            (guard-component? target argument environment callables
                              (list expected))))]
    [`(Eliminate ,scrutinee (,branches ...))
     (define contexts
       (branch-contexts scrutinee branches environment callables))
     (and contexts
          (guard-component? target scrutinee environment callables)
          (for/and ([context (in-list contexts)])
            (and (not (memq target (third context)))
                 (guarded-body? target parameter-types observed-types
                                (first context) (second context)
                                callables))))]
    [`(UnionEliminate ,scrutinee (,branches ...))
     (define contexts
       (union-branch-contexts scrutinee branches environment callables))
     (and contexts
          (guard-component? target scrutinee environment callables)
          (for/and ([context (in-list contexts)])
            (and (not (memq target (third context)))
                 (guarded-body? target parameter-types observed-types
                                (first context) (second context)
                                callables))))]
    [_ #f]))

(define (guarded? core environment callables)
  (match core
    [`(Recur ,callable ,function (,parameters ...) ,body
             ,continuation)
     (define signature (lookup callables callable))
     ;; §4.4。形 ii の継続は包みを 1 段剥がしてから呼ぶ。形 i の継続は
     ;; 剥がさない。包みの数が署名と合わない継続は保護つきにしない。
     (define-values (continuation-function arguments region-arguments)
       (match continuation
         [`(Apply (RegionApp ,g (,rhos ...)) ,args ...)
          (values g args rhos)]
         [`(Apply ,g ,args ...) (values g args #f)]
         [_ (values #f '() #f)]))
     (define region-arity-ok?
       (if region-arguments
           (= (length region-arguments)
              (length (forall-region-params signature)))
           (null? (forall-region-params signature))))
     (define contexts
       (callable-contexts callable function parameters
                          environment callables))
     (match (peel-forall-region signature)
       [`(NFn ,parameter-types ,_ ,_ ,latent-row ,_ ,_)
        ;; 本体の側だけ署名の包みを外す。継続側は元の署名を見て、形 ii では
        ;; RegionApp がその包みを明示的に剥がす。
        (define stripped
          (and contexts
               (strip-owned-prefix callable parameters body
                                   (first contexts) callables)))
        (and contexts
             stripped
             region-arity-ok?
             (eq? continuation-function function)
             (= (length arguments) (length parameter-types))
             (guarded-body? function parameter-types
                            (yield-types latent-row)
                            (first stripped) (second stripped) callables)
             (for/and ([argument (in-list arguments)]
                       [expected (in-list parameter-types)])
               (guard-component? function argument
                                 (second contexts) callables
                                 (list expected))))]
       [_ #f])]
    [_ #f]))

(define (classify-recur-body function parameters body-in environment callables)
  ;; span.md §7.3: 分類は span を見ない。入口で一度だけ投影する。
  (define body (erase-core body-in))
  (define signature (lookup environment function))
  (cond
    [(and (not (uses-seen? (target-uses function body)))
          (pre? function body environment callables))
     '(Finite no-self-reference)]
    [(structural-body? function parameters body environment callables)
     '(Finite structural)]
    [(match (and signature (peel-forall-region signature))
       [`(NFn ,parameter-types ,_ ,_ ,latent-row ,_ ,_)
        (and (= (length parameters) (length parameter-types))
             (guarded-body? function parameter-types
                            (yield-types latent-row)
                            body environment callables))]
       [_ #f])
     '(Productive guarded)]
    [else 'Unknown]))

(define (classify core-in environment callables)
  ;; span.md §7.3: 分類は span を見ない。入口で一度だけ投影する。
  (define core (erase-core core-in))
  (cond
    [(and (no-recursion? core)
          (pre? no-target core environment callables))
     '(Finite no-recursion)]
    [(no-self-reference? core environment callables)
     '(Finite no-self-reference)]
    [(structural? core environment callables) '(Finite structural)]
    [(guarded? core environment callables) '(Productive guarded)]
    [else 'Unknown]))
