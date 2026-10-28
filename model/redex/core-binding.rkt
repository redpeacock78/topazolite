#lang racket

(require racket/match
         racket/set
         redex/reduction-semantics
         "lang.rkt")

(provide core-children core-with-children
         raw-free-vars raw-subst* raw-alpha-equivalent?
         raw-static-symbols raw-symbols)

;; 意味的な子。c の位置に来る部分項だけが子である
;; （docs/specification/region.md §3）。
;; span、束縛子、型注釈、label、op、O、cid、π、構築子名 K は子に数えない。
;; 子の並びは項の書き順に従う。
;;
;; Construct と Rec は c 側と v 側で同じ形を持つため、1 つの節が両方を受ける。
;; 形が同じでも production は 2 つあり、その網羅は試験の側で押さえる。
(define (core-children t)
  (match t
    [`(Apply ,c_f ,c_a ...) (cons c_f c_a)]
    [`(Let (,_ ...) ,c_1 ,c_2) (list c_1 c_2)]
    [`(Construct ,_ ,_ ,cs ...) cs]
    [`(UnionInject ,_ ,_ ,payload) (list payload)]
    [`(UnionVal ,_ ,_ ,payload) (list payload)]
    [`(UnionEliminate ,scrutinee ,branches)
     (cons scrutinee (map last branches))]
    [`(UnionEliminateAt ,scrutinee ,branches)
     (cons scrutinee (map last branches))]
    [`(RecRewrite ,input (,entries ...))
     (cons input (map last entries))]
    [`(RecRewriteOpen (,fields ...)) (map last fields)]
    [`(Eliminate ,c ,brs)
     (cons c (for/list ([br (in-list brs)]) (last br)))]
    [`(EliminateAt ,c ,branches)
     (cons c (for/list ([branch (in-list branches)]) (last branch)))]
    [`(Perform ,_ ,c) (list c)]
    [`(Handle ,_ ,h ,c) (list (last h) c)]
    [`(Scope ,_ ,c) (list c)]
    [`(Recur ,_ ,_ ,_ ,c_1 ,c_2) (list c_1 c_2)]
    [`(Yield ,c_1 ,c_2) (list c_1 c_2)]
    [`(Suspend ,c) (list c)]
    [`(Drop ,c) (list c)]
    [`(Curry ,c_1 ,c_2) (list c_1 c_2)]
    [`(Rec ((,_ ,_ ,cs) ...)) cs]
    [`(Absent ,_) '()]
    [`(Proj ,c ,_) (list c)]
    [`(ProjOpt ,_ ,c ,_) (list c)]
    [`(Discharge (ProofRep ,_ ,_) ,c) (list c)]
    [`(Discharge (ProofRep ,_ ,_ ,_) ,c) (list c)]
    [`(Lam ,_ ,_ ,_ ,c) (list c)]
    [`(RecurVal ,_ ,_ ,_ ,c) (list c)]
    [`(UVal ,v) (list v)]
    [`(RVal (ProofRep ,_ ,_) ,v) (list v)]
    [`(CurryVal ,_ ,v_1 ,v_2) (list v_1 v_2)]
    [`(OwnedLeaf ,_ ,payload) (list payload)]
    [`(OwnedTransit ,_ ,payload) (list payload)]
    [`(OwnLeaf ,c) (list c)]
    [`(Reborrow ,c) (list c)]
    [`(ReborrowAt ,_ ,c) (list c)]
    [`(ProjBorrow ,c ,_) (list c)]
    [`(ProjBorrowAt ,_ ,c ,_) (list c)]
    [`(Read ,c) (list c)]
    [`(Assign ,target ,value) (list target value)]
    [`(Reassign ,_ ,_flow-type ,value) (list value)]
    [`(RegionLam (,_ ...) ,c) (list c)]
    [`(RegionApp ,c (,_ ...)) (list c)]
    [`(AddressOf ,c) (list c)]
    [`(RawLoad ,c) (list c)]
    [`(Unsafe ,c) (list c)]
    [`(PtrOffset ,c_1 ,c_2) (list c_1 c_2)]
    [`(RawStore ,target ,value) (list target value)]
    [`(FromRawPtr ,c ,_) (list c)]
    [`(PtrVal ,_ ,_ ,_) '()]
    [`(Borrow ,_) '()]
    [`(BorrowMut ,_) '()]
    [`(BorrowAt ,_ ,_ ,_) '()]
    [`(BorrowMutAt ,_ ,_ ,_) '()]
    [`(BorrowRef ,_ ,_ ,_) '()]
    [`(BorrowMutRef ,_ ,_ ,_) '()]
    [`(MutSlot ,_) '()]
    [`(Error ,_) '()]
    [`(Move ,_) '()]
    [`(Forward ,_) '()]
    [`(PrimVal ,_ ,_) '()]
    [`(TypeRep ,_ ,_ ,_) '()]
    [`(ProofRep ,_ ,_) '()]
    [`(resource ,_) '()]
    [(? exact-integer?) '()]
    [(? string?) '()]
    [(? symbol? s)
     #:when (or (redex-match? G2 x s) (redex-match? G2 l s))
     '()]
    [other (error 'core-children "Core の形ではない: ~s" other)]))

;; core-children の逆。子の並びを差し替えた同じ形を返す。
;; 節の並びは core-children と 1 対 1 で対応させる。片方だけ足すと
;; annotate-regions が子を落とす。
(define (core-with-children t children)
  (define (first-child) (first children))
  (match t
    [`(Apply ,_ ,_ ...) `(Apply ,@children)]
    [`(Let ,binder ,_ ,_) `(Let ,binder ,(first children) ,(second children))]
    [`(Construct ,τ ,K ,_ ...) `(Construct ,τ ,K ,@children)]
    [`(UnionInject ,union-type ,member-type ,_)
     `(UnionInject ,union-type ,member-type ,(first-child))]
    [`(UnionVal ,union-type ,member-type ,_)
     `(UnionVal ,union-type ,member-type ,(first-child))]
    [`(UnionEliminate ,_ ,branches)
     `(UnionEliminate ,(first children)
                      ,(for/list ([branch (in-list branches)]
                                  [body (in-list (rest children))])
                         (append (drop-right branch 1) (list body))))]
    [`(UnionEliminateAt ,_ ,branches)
     `(UnionEliminateAt ,(first children)
                        ,(for/list ([branch (in-list branches)]
                                    [body (in-list (rest children))])
                           (append (drop-right branch 1) (list body))))]
    [`(RecRewrite ,_ (,entries ...))
     `(RecRewrite ,(first children)
                  ,(for/list ([entry (in-list entries)]
                              [body (in-list (rest children))])
                     (append (drop-right entry 1) (list body))))]
    [`(RecRewriteOpen (,fields ...))
     `(RecRewriteOpen
       ,(for/list ([field (in-list fields)] [child (in-list children)])
          (append (drop-right field 1) (list child))))]
    [`(Eliminate ,_ ,brs)
     `(Eliminate ,(first children)
                 ,(for/list ([br (in-list brs)] [c (in-list (rest children))])
                    (append (drop-right br 1) (list c))))]
    [`(EliminateAt ,_ ,branches)
     `(EliminateAt ,(first children)
                   ,(for/list ([branch (in-list branches)]
                               [body (in-list (rest children))])
                      (append (drop-right branch 1) (list body))))]
    [`(Perform ,op ,_) `(Perform ,op ,(first-child))]
    [`(Handle ,op ,h ,_)
     `(Handle ,op
              ,(append (drop-right h 1) (list (first children)))
              ,(second children))]
    [`(Scope ,π ,_) `(Scope ,π ,(first-child))]
    [`(Recur ,cid ,f ,xs ,_ ,_)
     `(Recur ,cid ,f ,xs ,(first children) ,(second children))]
    [`(Yield ,_ ,_) `(Yield ,(first children) ,(second children))]
    [`(Suspend ,_) `(Suspend ,(first-child))]
    [`(Drop ,_) `(Drop ,(first-child))]
    [`(Curry ,_ ,_) `(Curry ,(first children) ,(second children))]
    [`(Rec ((,ls ,ms ,_) ...)) `(Rec ,(map list ls ms children))]
    [`(Proj ,_ ,label) `(Proj ,(first-child) ,label)]
    [`(ProjOpt ,τ ,_ ,label) `(ProjOpt ,τ ,(first-child) ,label)]
    [`(Discharge ,proof-rep ,_) `(Discharge ,proof-rep ,(first-child))]
    [`(Lam ,O ,cid ,xs ,_) `(Lam ,O ,cid ,xs ,(first-child))]
    [`(RecurVal ,cid ,f ,xs ,_) `(RecurVal ,cid ,f ,xs ,(first-child))]
    [`(UVal ,_) `(UVal ,(first-child))]
    [`(RVal ,proof-rep ,_) `(RVal ,proof-rep ,(first-child))]
    [`(CurryVal ,O ,_ ,_) `(CurryVal ,O ,(first children) ,(second children))]
    [`(OwnedLeaf ,tk ,_) `(OwnedLeaf ,tk ,(first-child))]
    [`(OwnedTransit ,p ,_) `(OwnedTransit ,p ,(first-child))]
    [`(OwnLeaf ,_) `(OwnLeaf ,(first-child))]
    [`(Reborrow ,_) `(Reborrow ,(first-child))]
    [`(ReborrowAt ,ρ ,_) `(ReborrowAt ,ρ ,(first-child))]
    [`(ProjBorrow ,_ ,label) `(ProjBorrow ,(first-child) ,label)]
    [`(ProjBorrowAt ,ρ ,_ ,label)
     `(ProjBorrowAt ,ρ ,(first-child) ,label)]
    [`(Read ,_) `(Read ,(first-child))]
    [`(Assign ,_ ,_) `(Assign ,(first children) ,(second children))]
    [`(Reassign ,target ,flow-type ,_)
     `(Reassign ,target ,flow-type ,(first-child))]
    [`(RegionLam ,rps ,_) `(RegionLam ,rps ,(first-child))]
    [`(RegionApp ,_ ,ρs) `(RegionApp ,(first-child) ,ρs)]
    [`(AddressOf ,_) `(AddressOf ,(first-child))]
    [`(RawLoad ,_) `(RawLoad ,(first-child))]
    [`(Unsafe ,_) `(Unsafe ,(first-child))]
    [`(PtrOffset ,_ ,_) `(PtrOffset ,(first children) ,(second children))]
    [`(RawStore ,_ ,_) `(RawStore ,(first children) ,(second children))]
    [`(FromRawPtr ,_ ,ρ) `(FromRawPtr ,(first-child) ,ρ)]
    [_
     (unless (null? children)
       (error 'core-with-children "子を持たない形へ子を与えた: ~s" t))
     t]))

(define (core-variable? value)
  (and (symbol? value) (redex-match? G2 x value)))

(define (as-variable-set value)
  (if (core-variable? value) (set value) (set)))

(define (without names values)
  (set-subtract values (list->set names)))

(define (branch-scope branch)
  (match branch
    [`(,_ (,names ...) -> ,body) (values names body)]
    [`(,_ (,names ...) (,_ ...) -> ,body) (values names body)]
    [other (error 'raw-free-vars "不正な Eliminate branch: ~s" other)]))

(define (union-branch-scope branch)
  (match branch
    [`(,_ ,name -> ,body) (values (list name) body)]
    [`(,_ ,name ,_ -> ,body) (values (list name) body)]
    [other (error 'raw-free-vars "不正な UnionEliminate branch: ~s" other)]))

(define (raw-free-vars core)
  (let walk ([term core])
    (define (branch-free branch get-scope)
      (define-values (names body) (get-scope branch))
      (without names (walk body)))
    (match term
      [`(Lam ,_ ,_ (,parameters ...) ,body)
       (without parameters (walk body))]
      [`(RecurVal ,_ ,f (,parameters ...) ,body)
       (without (cons f parameters) (walk body))]
      [`(Recur ,_ ,f (,parameters ...) ,body ,continuation)
       (set-union (without (cons f parameters) (walk body))
                  (without (list f) (walk continuation)))]
      [`(Let (,name ,_ ,_) ,bound ,body)
       (set-union (walk bound) (without (list name) (walk body)))]
      [`(Let (,name ,_) ,bound ,body)
       (set-union (walk bound) (without (list name) (walk body)))]
      [`(Eliminate ,scrutinee (,branches ...))
       (for/fold ([free (walk scrutinee)]) ([branch (in-list branches)])
         (set-union free (branch-free branch branch-scope)))]
      [`(EliminateAt ,scrutinee (,branches ...))
       (for/fold ([free (walk scrutinee)]) ([branch (in-list branches)])
         (set-union free (branch-free branch branch-scope)))]
      [`(UnionEliminate ,scrutinee (,branches ...))
       (for/fold ([free (walk scrutinee)]) ([branch (in-list branches)])
         (set-union free (branch-free branch union-branch-scope)))]
      [`(UnionEliminateAt ,scrutinee (,branches ...))
       (for/fold ([free (walk scrutinee)]) ([branch (in-list branches)])
         (set-union free (branch-free branch union-branch-scope)))]
      [`(RecRewrite ,input (,entries ...))
       (for/fold ([free (walk input)]) ([entry (in-list entries)])
         (match entry
           [`(,_ ,name ,_ ,_ ,_ ,body)
            (set-union free (without (list name) (walk body)))]))]
      [`(Handle ,_ (,name -> ,handler) ,body)
       (set-union (without (list name) (walk handler)) (walk body))]
      [`(Borrow ,w) (as-variable-set w)]
      [`(BorrowMut ,w) (as-variable-set w)]
      [`(BorrowAt ,_ (Own ,w-own ,_) ,w)
       (set-union (as-variable-set w) (as-variable-set w-own))]
      [`(BorrowMutAt ,_ (Own ,w-own ,_) ,w)
       (set-union (as-variable-set w) (as-variable-set w-own))]
      [`(Move ,w) (as-variable-set w)]
      [`(Forward ,w) (as-variable-set w)]
      [`(Reassign ,target ,_ ,value)
       (set-union (as-variable-set target) (walk value))]
      [(? core-variable? name) (set name)]
      [(? symbol?) (set)]
      [_
       (for/fold ([free (set)]) ([child (in-list (core-children term))])
         (set-union free (walk child)))])))

(define (raw-symbols value)
  (define (walk term)
    (cond
      [(symbol? term) (set term)]
      [(pair? term) (set-union (walk (car term)) (walk (cdr term)))]
      [(vector? term)
       (for/fold ([found (set)]) ([item (in-vector term)])
         (set-union found (walk item)))]
      [(box? term) (walk (unbox term))]
      [(hash? term)
       (for/fold ([found (set)]) ([(key item) (in-hash term)])
         (set-union found (walk key) (walk item)))]
      [else (set)]))
  (walk value))

(define (symbols-in value)
  (cond
    [(symbol? value) (list value)]
    [(pair? value) (append (symbols-in (car value)) (symbols-in (cdr value)))]
    [(vector? value) (append-map symbols-in (vector->list value))]
    [(box? value) (symbols-in (unbox value))]
    [(hash? value)
     (append-map (lambda (entry) (append (symbols-in (car entry))
                                         (symbols-in (cdr entry))))
                 (hash->list value))]
    [else '()]))

(define (raw-static-symbols core)
  (define (static . values) (append-map symbols-in values))
  (define (walk term)
    (match term
      [`(Apply ,callee ,arguments ...) (append-map walk (cons callee arguments))]
      [`(Let (,name ,type) ,bound ,body)
       (append (static type) (walk bound) (walk body))]
      [`(Let (,name ,bmode ,type) ,bound ,body)
       (append (static bmode type) (walk bound) (walk body))]
      [`(Construct ,type ,constructor ,fields ...)
       (append (static type constructor) (append-map walk fields))]
      [`(UnionInject ,union-type ,member-type ,payload)
       (append (static union-type member-type) (walk payload))]
      [`(UnionVal ,union-type ,member-type ,payload)
       (append (static union-type member-type) (walk payload))]
      [`(Eliminate ,scrutinee (,branches ...))
       (append (walk scrutinee)
               (append-map (lambda (branch)
                             (match branch
                               [`(,constructor (,_ ...) -> ,body)
                                (append (static constructor) (walk body))]))
                           branches))]
      [`(EliminateAt ,scrutinee (,branches ...))
       (append (walk scrutinee)
               (append-map (lambda (branch)
                             (match branch
                               [`(,constructor (,_ ...) (,annotations ...) -> ,body)
                                (append (static constructor annotations) (walk body))]))
                           branches))]
      [`(UnionEliminate ,scrutinee (,branches ...))
       (append (walk scrutinee)
               (append-map (lambda (branch)
                             (match branch
                               [`(,member-type ,_ -> ,body)
                                (append (static member-type) (walk body))]))
                           branches))]
      [`(UnionEliminateAt ,scrutinee (,branches ...))
       (append (walk scrutinee)
               (append-map (lambda (branch)
                             (match branch
                               [`(,member-type ,_ ,annotation -> ,body)
                                (append (static member-type annotation) (walk body))]))
                           branches))]
      [`(RecRewrite ,input (,entries ...))
       (append (walk input)
               (append-map (lambda (entry)
                             (match entry
                               [`(,label ,_ ,type ,mode ,extra-type ,body)
                                (append (static label type mode extra-type)
                                        (walk body))]))
                           entries))]
      [`(RecRewriteOpen (,fields ...))
       (append-map (lambda (field)
                     (match field
                       [`(,label ,mode ,body) (append (static label mode) (walk body))]
                       [`(,label ,mode ,type ,body)
                        (append (static label mode type) (walk body))]))
                   fields)]
      [`(Perform ,operation ,payload) (append (static operation) (walk payload))]
      [`(Handle ,operation (,_ -> ,handler) ,body)
       (append (static operation) (walk handler) (walk body))]
      [`(Scope ,π ,body) (append (static π) (walk body))]
      [`(Recur ,cid ,_ ,_ ,body ,continuation)
       (append (static cid) (walk body) (walk continuation))]
      [`(Yield ,first ,second) (append (walk first) (walk second))]
      [`(Suspend ,body) (walk body)]
      [`(Drop ,body) (walk body)]
      [`(Curry ,first ,second) (append (walk first) (walk second))]
      [`(Rec ((,label ,mode ,fields) ...))
       (append (static label mode) (append-map walk fields))]
      [`(Absent ,type) (static type)]
      [`(Proj ,body ,label) (append (walk body) (static label))]
      [`(ProjOpt ,type ,body ,label) (append (static type label) (walk body))]
      [`(Discharge ,proof ,body) (append (static proof) (walk body))]
      [`(Lam ,origin ,cid (,_ ...) ,body)
       (append (static origin cid) (walk body))]
      [`(RecurVal ,cid ,_ (,_ ...) ,body)
       (append (static cid) (walk body))]
      [`(UVal ,value) (walk value)]
      [`(RVal ,proof ,value) (append (static proof) (walk value))]
      [`(CurryVal ,origin ,first ,second)
       (append (static origin) (walk first) (walk second))]
      [`(OwnedLeaf ,token ,payload) (append (static token) (walk payload))]
      [`(OwnedTransit ,place ,payload) (append (static place) (walk payload))]
      [`(OwnLeaf ,body) (walk body)]
      [`(Borrow ,w) (if (core-variable? w) '() (static w))]
      [`(BorrowMut ,w) (if (core-variable? w) '() (static w))]
      [`(BorrowAt ,ρ (Own ,w ,fp) ,target)
       (append (static ρ fp)
               (if (core-variable? w) '() (static w))
               (if (core-variable? target) '() (static target)))]
      [`(BorrowMutAt ,ρ (Own ,w ,fp) ,target)
       (append (static ρ fp)
               (if (core-variable? w) '() (static w))
               (if (core-variable? target) '() (static target)))]
      [`(Reborrow ,body) (walk body)]
      [`(ReborrowAt ,ρ ,body) (append (static ρ) (walk body))]
      [`(ProjBorrow ,body ,label) (append (walk body) (static label))]
      [`(ProjBorrowAt ,ρ ,body ,label)
       (append (static ρ label) (walk body))]
      [`(Read ,body) (walk body)]
      [`(Assign ,target ,value) (append (walk target) (walk value))]
      [`(Reassign ,target ,flow-type ,value)
       (append (if (core-variable? target) '() (static target))
               (static flow-type) (walk value))]
      [`(RegionLam (,parameters ...) ,body)
       (append (static parameters) (walk body))]
      [`(RegionApp ,body (,regions ...))
       (append (walk body) (static regions))]
      [`(AddressOf ,body) (walk body)]
      [`(PtrOffset ,first ,second) (append (walk first) (walk second))]
      [`(RawLoad ,body) (walk body)]
      [`(RawStore ,target ,value) (append (walk target) (walk value))]
      [`(FromRawPtr ,body ,ρ) (append (walk body) (static ρ))]
      [`(Unsafe ,body) (walk body)]
      [`(BorrowRef ,place ,fp ,ρ) (static place fp ρ)]
      [`(BorrowMutRef ,place ,fp ,ρ) (static place fp ρ)]
      [`(PtrVal ,place ,fp ,type) (static place fp type)]
      [`(MutSlot ,place) (static place)]
      [`(Error ,place) (static place)]
      [`(Move ,w) (if (core-variable? w) '() (static w))]
      [`(Forward ,w) (if (core-variable? w) '() (static w))]
      [`(PrimVal ,origin ,name) (static origin name)]
      [`(TypeRep ,origin ,type ,kind) (static origin type kind)]
      [`(ProofRep ,origin ,proof) (static origin proof)]
      [`(resource ,number) (static number)]
      [(? symbol? symbol)
       (if (core-variable? symbol) '() (list symbol))]
      [(? exact-integer?) '()]
      [(? string?) '()]
      [_ (append-map walk (core-children term))]))
  (sort (walk core) symbol<?))

(define (raw-subst* core binders replacement-values)
  (if (or (not (list? binders))
          (not (list? replacement-values))
          (not (= (length binders) (length replacement-values)))
          (not (andmap symbol? binders))
          (not (= (length binders) (length (remove-duplicates binders eq?))))
          (not (andmap core-variable? binders)))
      #f
      (let ()
        (define forbidden
          (for/fold ([all (raw-symbols core)])
                    ([value (in-list replacement-values)])
            (set-union all (raw-symbols value))))
        (define counter 0)
        (define (fresh-name base)
          (let loop ()
            (define candidate (string->symbol (format "~a«~a»" base counter)))
            (set! counter (add1 counter))
            (if (set-member? forbidden candidate)
                (loop)
                (begin
                  (set! forbidden (set-add forbidden candidate))
                  candidate))))
        (define (remove-mappings mappings names)
          (filter (lambda (entry) (not (memq (car entry) names))) mappings))
        (define (replace-variable name mappings)
          (if (core-variable? name)
              (let ([entry (assq name mappings)]) (if entry (cdr entry) name))
              name))
        (define (scope-subst body names mappings)
          (define active (remove-mappings mappings names))
          (define inserted-free
            (for/fold ([free (set)]) ([entry (in-list active)])
              (set-union free (raw-free-vars (cdr entry)))))
          (define-values (names* body*)
            (for/fold ([renamed-names names] [current body])
                      ([name (in-list names)] [index (in-naturals)])
              (if (set-member? inserted-free name)
                  (let ([fresh (fresh-name name)])
                    (values (for/list ([candidate (in-list renamed-names)]
                                       [i (in-naturals)])
                              (if (= i index) fresh candidate))
                            (walk current (list (cons name fresh)))))
                  (values renamed-names current))))
          (values names* (walk body* active)))
        (define (subst-branch branch mappings)
          (match branch
            [`(,constructor (,names ...) -> ,body)
             (define-values (names* body*) (scope-subst body names mappings))
             `(,constructor ,names* -> ,body*)]
            [`(,constructor (,names ...) (,annotations ...) -> ,body)
             (define-values (names* body*) (scope-subst body names mappings))
             `(,constructor ,names* ,annotations -> ,body*)]
            [other (error 'raw-subst* "不正な Eliminate branch: ~s" other)]))
        (define (subst-union-branch branch mappings)
          (match branch
            [`(,member-type ,name -> ,body)
             (define-values (names* body*) (scope-subst body (list name) mappings))
             `(,member-type ,(first names*) -> ,body*)]
            [`(,member-type ,name ,annotation -> ,body)
             (define-values (names* body*) (scope-subst body (list name) mappings))
             `(,member-type ,(first names*) ,annotation -> ,body*)]
            [other (error 'raw-subst* "不正な UnionEliminate branch: ~s" other)]))
        (define (walk-recur cid f parameters body continuation mappings)
          (define active-body (remove-mappings mappings (cons f parameters)))
          (define active-continuation (remove-mappings mappings (list f)))
          (define f-captured?
            (for/or ([entry (in-list (append active-body active-continuation))])
              (set-member? (raw-free-vars (cdr entry)) f)))
          (define f* (if f-captured? (fresh-name f) f))
          (define body* (if f-captured?
                            (walk body (list (cons f f*)))
                            body))
          (define continuation*
            (if f-captured? (walk continuation (list (cons f f*))) continuation))
          (define-values (parameters* body**)
            (scope-subst body* parameters active-body))
          `(Recur ,cid ,f* ,parameters*
                  ,body**
                  ,(walk continuation* active-continuation)))
        (define mappings (map cons binders replacement-values))
        (define (walk term mappings)
          (match term
            [`(Lam ,origin ,cid (,parameters ...) ,body)
             (define-values (parameters* body*)
               (scope-subst body parameters mappings))
             `(Lam ,origin ,cid ,parameters* ,body*)]
            [`(RecurVal ,cid ,f (,parameters ...) ,body)
             (define-values (names* body*)
               (scope-subst body (cons f parameters) mappings))
             `(RecurVal ,cid ,(first names*) ,(rest names*) ,body*)]
            [`(Recur ,cid ,f (,parameters ...) ,body ,continuation)
             (walk-recur cid f parameters body continuation mappings)]
            [`(Let (,name ,type) ,bound ,body)
             (define-values (names* body*) (scope-subst body (list name) mappings))
             `(Let (,(first names*) ,type) ,(walk bound mappings) ,body*)]
            [`(Let (,name ,mode ,type) ,bound ,body)
             (define-values (names* body*) (scope-subst body (list name) mappings))
             `(Let (,(first names*) ,mode ,type) ,(walk bound mappings) ,body*)]
            [`(Eliminate ,scrutinee (,branches ...))
             `(Eliminate ,(walk scrutinee mappings)
                         ,(map (lambda (branch) (subst-branch branch mappings)) branches))]
            [`(EliminateAt ,scrutinee (,branches ...))
             `(EliminateAt ,(walk scrutinee mappings)
                           ,(map (lambda (branch) (subst-branch branch mappings)) branches))]
            [`(UnionEliminate ,scrutinee (,branches ...))
             `(UnionEliminate ,(walk scrutinee mappings)
                              ,(map (lambda (branch)
                                      (subst-union-branch branch mappings))
                                    branches))]
            [`(UnionEliminateAt ,scrutinee (,branches ...))
             `(UnionEliminateAt ,(walk scrutinee mappings)
                                ,(map (lambda (branch)
                                        (subst-union-branch branch mappings))
                                      branches))]
            [`(RecRewrite ,input (,entries ...))
             `(RecRewrite ,(walk input mappings)
                          ,(for/list ([entry (in-list entries)])
                             (match entry
                               [`(,label ,name ,type ,mode ,extra-type ,body)
                                (define-values (names* body*)
                                  (scope-subst body (list name) mappings))
                                `(,label ,(first names*) ,type ,mode ,extra-type ,body*)])))]
            [`(Handle ,operation (,name -> ,handler) ,body)
             (define-values (names* handler*)
               (scope-subst handler (list name) mappings))
             `(Handle ,operation (,(first names*) -> ,handler*)
                      ,(walk body mappings))]
            [`(Borrow ,w) `(Borrow ,(replace-variable w mappings))]
            [`(BorrowMut ,w) `(BorrowMut ,(replace-variable w mappings))]
            [`(BorrowAt ,rho (Own ,root ,fp) ,w)
             `(BorrowAt ,rho (Own ,(replace-variable root mappings) ,fp)
                        ,(replace-variable w mappings))]
            [`(BorrowMutAt ,rho (Own ,root ,fp) ,w)
             `(BorrowMutAt ,rho (Own ,(replace-variable root mappings) ,fp)
                           ,(replace-variable w mappings))]
            [`(Move ,w) `(Move ,(replace-variable w mappings))]
            [`(Forward ,w) `(Forward ,(replace-variable w mappings))]
            [`(Reassign ,target ,flow-type ,value)
             `(Reassign ,(replace-variable target mappings) ,flow-type
                        ,(walk value mappings))]
            [(? core-variable? name) (replace-variable name mappings)]
            [_
             (core-with-children term
                                 (map (lambda (child) (walk child mappings))
                                      (core-children term)))]))
        (walk core mappings))))

(struct alpha-name (index) #:transparent)

(define (raw-alpha-equivalent? left right)
  (define (normalize core)
    (define next-index 0)
    (define (fresh)
      (define result (alpha-name next-index))
      (set! next-index (add1 next-index))
      result)
    (define (lookup name env)
      (define entry (assq name env))
      (if entry (cdr entry) name))
    (define (extend names env)
      (for/fold ([markers '()] [extended env]) ([name (in-list names)])
        (define marker (fresh))
        (values (append markers (list marker)) (cons (cons name marker) extended))))
    (define (walk term env)
      (match term
        [`(Lam ,origin ,cid (,parameters ...) ,body)
         (define-values (markers env*) (extend parameters env))
         `(Lam ,origin ,cid ,markers ,(walk body env*))]
        [`(RecurVal ,cid ,f (,parameters ...) ,body)
         (define-values (markers env*) (extend (cons f parameters) env))
         `(RecurVal ,cid ,(first markers) ,(rest markers) ,(walk body env*))]
        [`(Recur ,cid ,f (,parameters ...) ,body ,continuation)
         (define marker-f (fresh))
         (define env-cont (cons (cons f marker-f) env))
         (define-values (markers env-body)
           (extend parameters env-cont))
         `(Recur ,cid ,marker-f ,markers
                 ,(walk body env-body)
                 ,(walk continuation env-cont))]
        [`(Let (,name ,type) ,bound ,body)
         (define marker (fresh))
         `(Let (,marker ,type) ,(walk bound env)
               ,(walk body (cons (cons name marker) env)))]
        [`(Let (,name ,mode ,type) ,bound ,body)
         (define marker (fresh))
         `(Let (,marker ,mode ,type) ,(walk bound env)
               ,(walk body (cons (cons name marker) env)))]
        [`(Eliminate ,scrutinee (,branches ...))
         `(Eliminate ,(walk scrutinee env)
                     ,(map (lambda (branch) (alpha-branch branch env)) branches))]
        [`(EliminateAt ,scrutinee (,branches ...))
         `(EliminateAt ,(walk scrutinee env)
                       ,(map (lambda (branch) (alpha-branch branch env)) branches))]
        [`(UnionEliminate ,scrutinee (,branches ...))
         `(UnionEliminate ,(walk scrutinee env)
                          ,(map (lambda (branch) (alpha-union-branch branch env))
                                branches))]
        [`(UnionEliminateAt ,scrutinee (,branches ...))
         `(UnionEliminateAt ,(walk scrutinee env)
                            ,(map (lambda (branch)
                                    (alpha-union-branch branch env))
                                  branches))]
        [`(RecRewrite ,input (,entries ...))
         `(RecRewrite ,(walk input env)
                      ,(for/list ([entry (in-list entries)])
                         (match entry
                           [`(,label ,name ,type ,mode ,extra-type ,body)
                            (define marker (fresh))
                            `(,label ,marker ,type ,mode ,extra-type
                                     ,(walk body (cons (cons name marker) env)))])))]
        [`(Handle ,operation (,name -> ,handler) ,body)
         (define marker (fresh))
         `(Handle ,operation
                  (,marker -> ,(walk handler (cons (cons name marker) env)))
                  ,(walk body env))]
        [`(Borrow ,w) `(Borrow ,(lookup w env))]
        [`(BorrowMut ,w) `(BorrowMut ,(lookup w env))]
        [`(BorrowAt ,rho (Own ,root ,fp) ,w)
         `(BorrowAt ,rho (Own ,(lookup root env) ,fp) ,(lookup w env))]
        [`(BorrowMutAt ,rho (Own ,root ,fp) ,w)
         `(BorrowMutAt ,rho (Own ,(lookup root env) ,fp) ,(lookup w env))]
        [`(Move ,w) `(Move ,(lookup w env))]
        [`(Forward ,w) `(Forward ,(lookup w env))]
        [`(Reassign ,target ,flow-type ,value)
         `(Reassign ,(lookup target env) ,flow-type ,(walk value env))]
        [(? core-variable? name) (lookup name env)]
        [_ (core-with-children term
                               (map (lambda (child) (walk child env))
                                    (core-children term)))]))
    (define (alpha-branch branch env)
      (match branch
        [`(,constructor (,names ...) -> ,body)
         (define-values (markers env*) (extend names env))
         `(,constructor ,markers -> ,(walk body env*))]
        [`(,constructor (,names ...) (,annotations ...) -> ,body)
         (define-values (markers env*) (extend names env))
         `(,constructor ,markers ,annotations -> ,(walk body env*))]))
    (define (alpha-union-branch branch env)
      (match branch
        [`(,member-type ,name -> ,body)
         (define-values (markers env*) (extend (list name) env))
         `(,member-type ,(first markers) -> ,(walk body env*))]
        [`(,member-type ,name ,annotation -> ,body)
         (define-values (markers env*) (extend (list name) env))
         `(,member-type ,(first markers) ,annotation -> ,(walk body env*))]))
    (walk core '()))
  (equal? (normalize left) (normalize right)))
