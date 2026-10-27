#lang racket

(require racket/match
         racket/set
         redex/reduction-semantics
         "lang.rkt"
         "borrow.rkt"
         "borrow-gen.rkt"
         "machine.rkt"
         "region.rkt"
         "span-core.rkt"
         "type-equiv.rkt")

(provide control-diff
         borrow-form-candidates
         borrow-value?
         rule-bucket
         (struct-out provenance)
         empty-provenance
         provenance-extend
         normalize-binder
         resolve-designator
         (struct-out bcounters)
         make-bcounters
         bcounters-zeros
         static-borrow-set
         static-match-verdict
         live-borrows
         check-no-move-of-live
         check-mut-exclusive
         check-reborrow-parents
         check-borrow-execution)

(define-metafunction G2m
  oracle-substitute : c x v -> any
  [(oracle-substitute c_body x v_arg)
   (substitute c_body (x v_arg))])

;; spec §4.5。oracle は typing.rkt と borrow.rkt の判定を一切呼ばない。
;; 呼ぶと静的な借用検査の言い換えになり、独立な照合の意味が消える。

(define (borrow-value? v)
  (match v
    [`(BorrowRef ,_ ,_ ,_) #t]
    [`(BorrowMutRef ,_ ,_ ,_) #t]
    [_ #f]))

(define (plain-ubr branch)
  (peel-ubr branch))

(define (annotated-data-branch-parts branches)
  (define-values (plain annotations)
    (peel-annotated-data-branches branches))
  (for/list ([branch (in-list plain)]
             [regions (in-list annotations)])
    (match (peel-branch branch)
      [`(,constructor (,binders ...) -> ,body)
       (and (list? regions)
            (= (length binders) (length regions))
            (list constructor binders regions body))]
      [_ #f])))

(define (annotated-union-branch-parts branches)
  (define-values (plain regions)
    (peel-annotated-union-branches branches))
  (for/list ([branch (in-list plain)]
             [region (in-list regions)])
    (match (peel-branch branch)
      [`(,member ,binder -> ,body)
       (and region (list (peel-ty member) (peel-bind binder) region body))]
      [_ #f])))

(define (annotation-rho annotation parent-rho)
  (if (eq? annotation '%parent) parent-rho annotation))

(define (matching-union-branch member-type branches)
  (for/first ([branch (in-list branches)]
              #:do [(define plain (plain-ubr branch))]
              #:when (match plain
                       [`(,branch-type ,_binder -> ,_body)
                        (type-equiv? member-type branch-type)]
                       [_ #f]))
    (plain-ubr branch)))

(define (record-field-value fields label)
  (and (not (check-duplicates (map first fields)))
       (for/first ([field (in-list fields)]
                   #:when (equal? (first field) label))
         (third field))))

(define (rec-rewrite-close-preserves? open-fields closed-fields)
  (and (= (length open-fields) (length closed-fields))
       (for/and ([open-field (in-list open-fields)]
                 [closed-field (in-list closed-fields)])
         (match* (open-field closed-field)
           [((list label mode value) (list label2 mode2 value2))
            (and (equal? label label2) (equal? mode mode2)
                 (equal? value value2))]
           [((list label mode _type value)
             (list label2 mode2 value2))
            (and (equal? label label2) (equal? mode mode2)
                 (equal? value value2))]
           [(_ _) #f]))))

;; 簡約前後の制御項について、差分をすべて含む最小の位置を求め、その位置の
;; 部分項の対を返す。制御項が等しいときだけ #f を返す。
;; 子が 2 つ以上異なる節点は、その節点自体が差分を含む最小の位置である。
;; 位置が根まで戻る場合も対は返す。構造が食い違う位置も、それ自体が最小の
;; 位置である。
(define (control-diff pre post)
  (cond
    [(equal? pre post) #f]
    [(and (list? pre) (list? post)
          (= (length pre) (length post)))
     (define differing
       (for/list ([a (in-list pre)]
                  [b (in-list post)]
                  [i (in-naturals)]
                  #:unless (equal? a b))
         i))
     (if (= (length differing) 1)
         (control-diff (list-ref pre (first differing))
                       (list-ref post (first differing)))
         (cons pre post))]
    [else (cons pre post)]))

(define (substitution-produced-borrow-values redex contractum rule-name)
  (define pairs (substitution-pairs rule-name redex contractum))
  (and pairs
       (let ([introduced
              (for/list ([pair (in-list pairs)]
                         #:when (borrow-value? (cdr pair)))
                (cdr pair))])
         (filter (lambda (value) (member value introduced equal?))
                 (collect-borrow-values contractum)))))

(define (borrowed-eliminate-children redex contractum rule-name)
  ;; 規則名なしの直接 probe は既存の構造判定を保つ。実 trace では規則名を渡す。
  (or (substitution-produced-borrow-values redex contractum rule-name)
      (and (not rule-name) (collect-borrow-values contractum))))

(define (data-elimination-approved tag place path rho children)
  (define expected
    (for/list ([child (in-list (or children '()))])
      (match child
        [(list (== tag) child-place child-path child-rho)
         #:when (and (equal? child-place place)
                     (= (length child-path) (add1 (length path)))
                     (equal? (take child-path (length path)) path)
                     (exact-nonnegative-integer? (last child-path)))
         (list 'derived
               (if (eq? tag 'BorrowMutRef) 'mut 'shared)
               place child-path child-rho place path rho)]
        [_ (list 'unverified)])))
  (if children expected (list (list 'unverified))))

(define (union-elimination-approved tag place path rho children)
  (define expected-path (append path '((Payload))))
  (define expected
    (for/list ([child (in-list (or children '()))])
      (match child
        [(list (== tag) child-place child-path child-rho)
         #:when (and (equal? child-place place)
                     (equal? child-path expected-path))
         (list 'derived
               (if (eq? tag 'BorrowMutRef) 'mut 'shared)
               place child-path child-rho place path rho)]
        [_ (list 'unverified)])))
  (if children expected (list (list 'unverified))))

;; spec §4.6。承認済みの redex と contractum の対の表。
;; 分類は根、派生、再借用、使用、未検証のいずれかである。
(define (approved-forms redex contractum rule-name)
  (match (list redex contractum)
    ;; R-RecRewrite-Open は入力欄を作業列へ一度ずつ移す。
    [(list `(RecRewrite ,_ ,_) `(RecRewriteOpen ,_)) '()]
    ;; R-RecRewrite-Close は作業欄の値を保ったまま Rec へ戻す。
    [(list `(RecRewriteOpen (,open-fields ...)) `(Rec (,closed-fields ...)))
     #:when (rec-rewrite-close-preserves? open-fields closed-fields)
     '()]
    ;; R-ScopeValue は finalization 後に値を unwrap するだけであり、借用値を
    ;; 保ったまま新しい借用形を作らない。
    [(list `(Scope ,_π ,value) value) '()]
    ;; R-Yield は観測 wrapper を外すだけであり、continuation 内の借用は
    ;; 新しい借用形ではない。
    [(list `(Yield ,_observed ,continuation) continuation) '()]
    ;; R-Proj は選んだ欄の値そのものを返す。
    [(list `(Proj (Rec (,fields ...)) ,label) contractum)
     #:when (equal? (record-field-value fields label) contractum)
     '()]
    ;; R-ProjOpt は選んだ欄の値を Some で包む。
    [(list `(ProjOpt ,type (Rec (,fields ...)) ,label)
           `(Construct (Option ,type2) some ,value))
     #:when (and (equal? type type2)
                 (equal? (record-field-value fields label) value))
     '()]
    ;; R-ProjOpt は Absent 欄を none へ変える。
    [(list `(ProjOpt ,type (Rec (,fields ...)) ,label)
           `(Construct (Option ,type2) none))
     #:when (and (equal? type type2)
                 (equal? (record-field-value fields label)
                         `(Absent ,type)))
     '()]
    ;; R-UnionInject は payload を変えずに runtime tag だけを付ける。
    [(list `(UnionInject ,union-type ,member-type ,payload)
           `(UnionVal ,union-type2 ,member-type2 ,payload2))
     #:when (and (equal? payload payload2)
                 (equal? (normalize-type union-type) union-type2)
                 (equal? (normalize-type member-type) member-type2))
     '()]
    ;; Owned Union の除去では、UnionVal 全体を保ったまま移送 marker だけを外す。
    [(list `(OwnedTransit ,_p (UnionVal ,τu ,τm ,v))
           `(UnionVal ,τu2 ,τm2 ,v2))
     #:when (and (eq? rule-name 'R-UnionEliminateTransit)
                 (equal? τu τu2) (equal? τm τm2) (equal? v v2))
     '()]
    [(list `(Eliminate (OwnedTransit ,_p ,value) ,branches)
           `(Eliminate ,value2 ,branches2))
     #:when (and (eq? rule-name 'R-EliminateTransit)
                 (equal? value value2) (equal? branches branches2))
     '()]
    [(list `(EliminateAt (OwnedTransit ,_p ,value) ,branches)
           `(EliminateAt ,value2 ,branches2))
     #:when (and (eq? rule-name 'R-EliminateAtTransit)
                 (equal? value value2) (equal? branches branches2))
     '()]
    [(list `(UnionEliminateAt
             (OwnedTransit ,_p (UnionVal ,τu ,τm ,v)) ,branches)
           `(UnionEliminateAt (UnionVal ,τu2 ,τm2 ,v2) ,branches2))
     #:when (and (eq? rule-name 'R-UnionEliminateAtTransit)
                 (equal? τu τu2) (equal? τm τm2) (equal? v v2)
                 (equal? branches branches2))
     '()]
    ;; R-RecurBind で再帰関数を使わない継続は、そのまま contractum になる。
    [(list `(Recur ,_ ,_ ,_ ,_ ,continuation) contractum)
     #:when (equal? continuation contractum)
     '()]
    ;; R-HandleValue は handler を使わず、結果値をそのまま返す。
    [(list `(Handle ,_ (,x -> ,handler) ,value) contractum)
     #:when (and (equal? value contractum)
                 (null? (collect-borrow-values handler)))
     '()]
    ;; R-HandleSkip は空の内側文脈にある Perform と payload をそのまま返す。
    [(list `(Handle ,op-handler (,x -> ,handler)
                    (Perform ,op-performed ,argument))
           `(Perform ,op-result ,argument-result))
     #:when (and (not (equal? op-handler op-performed))
                 (equal? op-performed op-result)
                 (equal? argument argument-result)
                 (null? (collect-borrow-values handler)))
     '()]
    ;; R-Suspend は継続を unwrap するだけである。
    [(list `(Suspend ,continuation) continuation) '()]
    ;; R-DischargeRemainder は strip-remainder が残す値をそのまま運ぶ。
    [(list `(Discharge
             (ProofRep ,_ (RemainderSafelyDropped ,actual ,expected)) ,value)
           contractum)
     #:when
     (match (strip-remainder actual expected value)
       [(list output _removed) (equal? output contractum)]
       [_ #f])
     '()]
    ;; 非 RSD の R-Discharge は検査済みの内側をそのまま返す。
    [(list `(Discharge (ProofRep ,_ ,proposition) ,inner) inner)
     #:when
     (match proposition
       [`(RemainderSafelyDropped ,_ ,_) #f]
       [_ #t])
     '()]
    [(list `(BorrowAt ,ρ (Own ,p ,fp) ,w)
           `(BorrowRef ,p2 ,fp2 ,ρ2))
     #:when (and (equal? p p2) (equal? fp fp2) (equal? ρ ρ2))
     (list (list 'root 'shared p fp ρ w))]
    [(list `(BorrowMutAt ,ρ (Own ,p ,fp) ,w)
           `(BorrowMutRef ,p2 ,fp2 ,ρ2))
     #:when (and (equal? p p2) (equal? fp fp2) (equal? ρ ρ2))
     (list (list 'root 'mut p fp ρ w))]
    [(list `(ReborrowAt ,ρ (BorrowMutRef ,pp ,fpp ,ρp))
           `(BorrowRef ,p2 ,fp2 ,ρ2))
     #:when (and (equal? ρ ρ2)
                 (equal? pp p2) (equal? fpp fp2))
     (list (list 'reborrow p2 fp2 ρ ρp))]
    [(list `(ProjBorrowAt ,ρ (BorrowRef ,pp ,fpp ,ρp) ,label)
           `(,tag2 ,p2 ,fp2 ,ρ2))
     #:when (and (eq? tag2 'BorrowRef)
                 (equal? pp p2)
                 (equal? fp2 (append fpp (list label)))
                 (equal? ρp ρ2))
     (list (list 'derived
                 'shared
                 p2 fp2 ρ2 pp fpp ρp))]
    [(list `(ProjBorrowAt ,ρ (BorrowMutRef ,pp ,fpp ,ρp) ,label)
           `(,tag2 ,p2 ,fp2 ,ρ2))
     #:when (and (memq tag2 '(BorrowRef BorrowMutRef))
                 (equal? pp p2)
                 (equal? fp2 (append fpp (list label)))
                 (equal? ρ ρ2))
     (list (list 'derived
                 (if (eq? tag2 'BorrowMutRef) 'mut 'shared)
                 p2 fp2 ρ2 pp fpp ρp))]
    ;; Eliminate は scrutinee と各 child の tag を同じものとして一般化する。
    ;; 共有・可変の片側だけを承認すると、規則名と借用 mode の不一致を隠す。
    [(list `(Eliminate (,tag ,p ,fp ,ρ) ,_ ...) contractum)
     #:when (memq tag '(BorrowRef BorrowMutRef))
     (data-elimination-approved
      tag p fp ρ (borrowed-eliminate-children redex contractum rule-name))]
    [(list `(EliminateAt (,tag ,p ,fp ,ρ) ,_ ...) contractum)
     #:when (memq tag '(BorrowRef BorrowMutRef))
     (data-elimination-approved
      tag p fp ρ (borrowed-eliminate-children redex contractum rule-name))]
    [(list `(UnionEliminate (,tag ,p ,fp ,ρ) ,_ ...) contractum)
     #:when (memq tag '(BorrowRef BorrowMutRef))
     (union-elimination-approved
      tag p fp ρ (borrowed-eliminate-children redex contractum rule-name))]
    [(list `(UnionEliminateAt (,tag ,p ,fp ,ρ) ,_ ...) contractum)
     #:when (memq tag '(BorrowRef BorrowMutRef))
     (union-elimination-approved
      tag p fp ρ (borrowed-eliminate-children redex contractum rule-name))]
    [(list `(Read (,tag ,p ,fp ,ρ)) _)
     #:when (memq tag '(BorrowRef BorrowMutRef))
     (list (list 'use (if (eq? tag 'BorrowMutRef) 'mut 'shared) p fp ρ))]
    [(list `(Assign (BorrowMutRef ,p ,fp ,ρ) ,_) 'unit)
     (list (list 'use 'mut p fp ρ))]
    [_ #f]))

;; contractum の中の借用値をすべて拾う。
(define (collect-borrow-values t)
  (cond
    [(borrow-value? t) (list t)]
    [(list? t) (append* (map collect-borrow-values t))]
    [else '()]))

;; spec §4.6。照合できず、しかも redex か contractum に借用値が現れるなら
;; unverified を返して失敗させる。借用値が無い遷移は非借用遷移として扱う。
(define (borrow-form-candidates redex contractum #:rule [rule-name #f])
  (define matched (approved-forms redex contractum rule-name))
  (cond
    ;; 承認済みの非生成形は空 list で表す。未知の借用遷移を表す #f と区別する。
    [(list? matched) matched]
    [(or (pair? (collect-borrow-values redex))
         (pair? (collect-borrow-values contractum)))
     (list (list 'unverified))]
    [else '()]))

;; spec §4.6。置換を行う規則。ここから記号と place の対応を取る。
;; -->g2/rules は -->g1/rules を extend-reduction-relation で拡張しており、
;; G1 側の名前も発火しうるので両方を挙げる。
(define substituting-rule-names
  (seteq 'R-Beta 'R-Let 'R-LetB 'R-LetIdentity 'R-LetIdentityB
         'R-LetOwned 'R-LetOwnedB 'R-LetMutB
         'R-Eliminate 'R-EliminateRef 'R-EliminateMutRef 'R-UnionEliminate
         'R-EliminateAt 'R-EliminateAtRef 'R-EliminateAtMutRef
         'R-UnionEliminateRef 'R-UnionEliminateMutRef
         'R-UnionEliminateAt 'R-UnionEliminateAtRef 'R-UnionEliminateAtMutRef
         'R-RecurUnfold 'R-HandleReturn))

;; spec §4.6。置換を行わない規則。名前が増えたときに黙って取りこぼさないよう
;; 明示的に挙げ、どちらにも無い名前は unknown として検査を失敗させる。
;; 二つの集合の和は -->g2/rules の 80 名と一致する。Step の回帰がこれを検査する。
(define non-substituting-rule-names
  (seteq 'R-Delta 'R-Proj 'R-ProjOpt 'R-ProjPlace 'R-ProjOptPlace
         'R-Drop 'R-Borrow 'R-BorrowError
         'R-BorrowMut 'R-BorrowMutError 'R-Reborrow
         'R-ProjBorrow 'R-ProjBorrowMut 'R-Read 'R-ReadMut 'R-Assign
         'R-ReadMutSlot 'R-Reassign
         'R-UnionInject 'R-RecRewrite-Open 'R-RecRewrite-Close
         'R-AddressOf 'R-PtrOffset 'R-RawLoad 'R-RawStore
         'R-FromRawPtrConst 'R-FromRawPtrMut 'R-UnsafeExit
         'R-Move 'R-MoveError 'R-Forward
         'R-ScopeValue 'R-ScopeError 'R-ScopeAbort
         'R-RecurBind 'R-RegionApp 'R-RegionAppRecur 'R-Yield 'R-Suspend 'R-Discharge
         'R-DischargeRemainder 'R-OwnLeaf 'R-OwnLeafPass
         'R-CurryVal 'R-ApplyCurry
         'R-ApplyTransit 'R-EliminateTransit 'R-UnionEliminateTransit
         'R-EliminateAtTransit 'R-UnionEliminateAtTransit
         'R-CurryTransit 'R-OwnLeafTransit
         'R-HandleValue 'R-HandleSkip 'R-HandleError
         'R-RetireValue 'R-RetireError 'R-RetirePerform))

(define (rule-bucket name)
  (cond [(set-member? substituting-rule-names name) 'substituting]
        [(set-member? non-substituting-rule-names name) 'non-substituting]
        [else 'unknown]))

;; spec §4.6。記号から place への多価の対応。
(struct provenance (table) #:transparent)

(define (empty-provenance) (provenance (hash)))

;; 束縛出現の識別子。Redex の substitute が末尾へ付ける «N» の並びだけを
;; 取り除く。錨付きなので 1 回だけ当たり、⟨N⟩ には触れない。
;; shadowing した束縛子は ⟨N⟩ で区別されるため、base 名が同じでも同じ鍵へ畳まれない。
;; 一意化前の綴りへ戻すのは uniquify.rkt の binder-base の仕事である。
(define normalize-rx #px"(«[0-9]+»)+$")

(define (normalize-binder name)
  (if (symbol? name)
      (string->symbol
       (regexp-replace normalize-rx (symbol->string name) ""))
      name))

(define (provenance-add prov name place)
  (provenance
   (hash-update (provenance-table prov) (normalize-binder name)
                (lambda (s) (set-add s place))
                (set))))

(define (resolve-designator prov w)
  (cond
    [(exact-nonnegative-integer? w) (list w)]
    [(symbol? w)
     (set->list
      (hash-ref (provenance-table prov) (normalize-binder w) (set)))]
    [else '()]))

(define (cfg-parts config)
  (match config
    [`(cfg ,core ,H ,Ω ,Λtok ,θ) (list core H Ω Λtok θ)]
    [_ #f]))

(define (table-keys tbl)
  (for/set ([entry (in-list tbl)]) (first entry)))

;; 裸の自然数は整数リテラルとも place とも読める。Ω の鍵に現れる値だけを
;; place の候補として扱う。取りこぼしは起きず、余分な対応が入りうるだけ。
(define (place-candidates v known-places)
  (cond
    [(and (exact-nonnegative-integer? v) (set-member? known-places v))
     (list v)]
    [(borrow-value? v) (list (second v))]
    [else '()]))

;; branch の形は (K (x ...) -> c) である。
(define (branches-for K branches)
  (for/list ([br (in-list branches)]
             #:when (equal? (first br) K))
    br))

(define (branch-binders K branches)
  (define found (branches-for K branches))
  ;; 同じ K の枝が 2 つ以上あると枝が一意に定まらないので #f を返し、
  ;; 呼び出し側が fail させる。
  (and (= (length found) 1) (second (first found))))

(define (union-branch-bindings member-type branches)
  (define branch (matching-union-branch member-type branches))
  (match branch
    [`(,_member ,binder -> ,_body) (list binder)]
    [_ #f]))

;; spec §4.6。置換規則の redex から (記号 . 値) の対を取り出す。
;; 取り出せない形なら #f を返し、呼び出し側が fail させる。
(define (substitution-pairs name redex contractum)
  (match (list name redex)
    [(list 'R-LetIdentity `(Let (,x ,_τ) ,v-bound ,x))
     (list (cons x v-bound))]
    [(list 'R-LetIdentityB `(Let (,x ,_bmode ,_τ) ,v-bound ,x))
     (list (cons x v-bound))]
    [(list (or 'R-Let 'R-LetB) `(Let (,x ,_bmode ,_τ) ,v-bound ,_body))
     (list (cons x v-bound))]
    [(list 'R-Beta `(Apply (Lam ,_O ,_cid (,x ...) ,_body) ,v ...))
     #:when (= (length x) (length v))
     (map cons x v)]
    [(list 'R-RecurUnfold
           `(Apply (RecurVal ,_cid ,f (,x ...) ,_body) ,v ...))
     #:when (= (length x) (length v))
     ;; f へ束縛されるのは RecurVal 自身であり place ではない。
     (cons (cons f 'not-a-place) (map cons x v))]
    [(list 'R-Eliminate `(Eliminate (Construct ,_τ ,K ,v ...) ,branches))
     (define binders (branch-binders K branches))
     (and binders (= (length binders) (length v)) (map cons binders v))]
    [(list 'R-EliminateAt
           `(EliminateAt (Construct ,_τ ,K ,v ...) ,branches))
     (define binders
       (for/first ([parts (in-list (annotated-data-branch-parts branches))]
                   #:when (and parts (eq? K (first parts))))
         (second parts)))
     (and binders (= (length binders) (length v)) (map cons binders v))]
    [(list 'R-UnionEliminate
           `(UnionEliminate (UnionVal ,_union-type ,member-type ,payload)
                           ,branches))
     (define binders (union-branch-bindings member-type branches))
     (and binders (= (length binders) 1)
          (list (cons (first binders) payload)))]
    [(list 'R-UnionEliminateAt
           `(UnionEliminateAt
             (UnionVal ,_union-type ,member-type ,payload) ,branches))
     (define branch
       (for/first ([parts
                    (in-list (annotated-union-branch-parts branches))]
                   #:when (and parts (type-equiv? member-type (first parts))))
         parts))
     (and branch (list (cons (second branch) payload)))]
    [(list (and rule (or 'R-EliminateRef 'R-EliminateMutRef))
           `(Eliminate (,tag ,p ,fp ,ρ) ,branches))
     #:when (equal? tag
                    (if (eq? rule 'R-EliminateMutRef)
                        'BorrowMutRef
                        'BorrowRef))
     ;; 束縛子へ渡るのは欄を指す借用参照であり、規則が組み立てる。
     ;; contractum は本体が実際に使った欄しか含まないため、出現した参照の
     ;; arity だけでは未使用の束縛子を復元できない。各枝の本体へ位置順の
     ;; 参照を同時置換して contractum と比較し、合致した全候補を合併する。
     (define (child-ref i) (list tag p (append fp (list i)) ρ))
     (define matching
       (for/list ([b (in-list branches)]
                  #:when (and (list? b)
                               (= (length b) 4)
                               (list? (second b))
                               (eq? (third b) '->))
                  #:do [(define binders (second b))]
                  #:when (branch-substitution-matches?
                          (fourth b)
                          binders
                          (for/list ([i (in-range (length binders))])
                            (child-ref i))
                          contractum))
         (for/list ([x (in-list (second b))]
                    [i (in-naturals 0)])
           (cons x (child-ref i)))))
     (if (null? matching) #f (apply append matching))]
    [(list (and rule (or 'R-EliminateAtRef 'R-EliminateAtMutRef))
           `(EliminateAt (,tag ,p ,fp ,ρ) ,branches))
     #:when (equal? tag
                    (if (eq? rule 'R-EliminateAtMutRef)
                        'BorrowMutRef
                        'BorrowRef))
     (define matching
       (for/list ([parts (in-list (annotated-data-branch-parts branches))]
                  #:when
                  (and parts
                       (let* ([binders (second parts)]
                              [annotations (third parts)]
                              [body (fourth parts)]
                              [child-refs
                               (for/list ([i (in-range (length binders))]
                                          [annotation
                                           (in-list annotations)])
                                 (list tag p (append fp (list i))
                                       (annotation-rho annotation ρ)))])
                         (branch-substitution-matches?
                          body binders child-refs contractum))))
         (define binders (second parts))
         (define annotations (third parts))
         (for/list ([x (in-list binders)]
                    [i (in-naturals)]
                    [annotation (in-list annotations)])
           (cons x (list tag p (append fp (list i))
                         (annotation-rho annotation ρ))))))
     (if (null? matching) #f (apply append matching))]
    [(list (and rule (or 'R-UnionEliminateRef 'R-UnionEliminateMutRef))
           `(UnionEliminate (,tag ,p ,fp ,ρ) ,branches))
     #:when (equal? tag
                    (if (eq? rule 'R-UnionEliminateMutRef)
                        'BorrowMutRef
                        'BorrowRef))
     (define child-ref
       (list tag p (append fp '((Payload))) ρ))
     (define matching
       (filter
        values
        (for/list ([branch (in-list branches)])
          (match (plain-ubr branch)
            [`(,_member ,binder -> ,body)
             (and (branch-substitution-matches?
                   body (list binder) (list child-ref) contractum)
                  (list (cons binder child-ref)))]
            [_ #f]))))
     (if (null? matching) #f (apply append matching))]
    [(list (and rule
                (or 'R-UnionEliminateAtRef 'R-UnionEliminateAtMutRef))
           `(UnionEliminateAt (,tag ,p ,fp ,ρ) ,branches))
     #:when (equal? tag
                    (if (eq? rule 'R-UnionEliminateAtMutRef)
                        'BorrowMutRef
                        'BorrowRef))
     (define child-ref
       (lambda (annotation)
         (list tag p (append fp '((Payload)))
               (annotation-rho annotation ρ))))
     (define matching
       (filter
        values
        (for/list ([parts (in-list (annotated-union-branch-parts branches))])
          (match parts
            [(list _member binder annotation body)
             (and (branch-substitution-matches?
                   body (list binder) (list (child-ref annotation)) contractum)
                  (list (cons binder (child-ref annotation))))]
            [_ #f]))))
     (if (null? matching) #f (apply append matching))]
    [(list 'R-HandleReturn
           `(Handle ,_op (,x -> ,handler) ,_inner))
     (define inferred (infer-substituted-value handler x contractum))
     (cond
       [(not inferred) #f]
       [(null? inferred) '()]
       [else (list (cons x (first inferred)))])]
    [_ #f]))

;; R-HandleReturn は handler 本体へ payload を置換した結果を返す。
;; F の走査を再現すると値の内部の Perform を誤って拾うため、redex 内の
;; handler 本体と contractum を逆向きに照合して実際の payload を復元する。
(define (infer-substituted-value body binder contractum)
  (define (substitute-payload value)
    (term (oracle-substitute ,body ,binder ,value)))
  (if (alpha-equivalent? G2m body (substitute-payload 'unit))
      '()
      (let ([candidates
             (let walk ([current contractum])
               (append (if (redex-match? G2m v current) (list current) '())
                       (if (pair? current)
                           (append (walk (car current)) (walk (cdr current)))
                           '())))])
        (define matches
          (for/list ([candidate (in-list (remove-duplicates candidates))]
                     #:when (alpha-equivalent?
                             G2m (substitute-payload candidate) contractum))
            candidate))
        (and (pair? matches)
             (andmap (lambda (candidate)
                       (alpha-equivalent? G2m (first matches) candidate))
                     (rest matches))
             (list (first matches))))))

;; 枝本体の束縛子を、機械と同じ束縛を考慮する置換で借用参照へ置き換える。
(define (substitute-branch-body body binders values)
  ;; G2m の Core 外の合成 fixture は候補不一致として扱う。
  (with-handlers ([exn:fail? (lambda (_) #f)])
    (term (substitute*/g2 ,body (,@binders) (,@values)))))

(define (branch-substitution-matches? body binders values contractum)
  (define substituted (substitute-branch-body body binders values))
  (and substituted (alpha-equivalent? G2m substituted contractum)))

;; spec §4.6。規則名で仕分け、置換規則なら記号と place の対応を足す。
;; 未知の規則、形が取り出せない置換規則、R-LetOwned 系の増分が想定外の場合は
;; fail を返し、その trace の検査を失敗させる。
(define (provenance-extend prov name pre post)
  (define pre-parts (cfg-parts pre))
  (define post-parts (cfg-parts post))
  (cond
    [(or (not pre-parts) (not post-parts)) 'fail]
    [else
     (define known-places (table-keys (third pre-parts)))
     (case (rule-bucket name)
       [(non-substituting) prov]
       [(unknown) 'fail]
       [(substituting)
        (cond
          [(memq name '(R-LetOwned R-LetOwnedB R-LetMutB))
           (extend-let-owned prov pre-parts post-parts)]
          [else
           (define diff (control-diff (first pre-parts) (first post-parts)))
           ;; 空の対応（束縛子を持たない枝）は正しい結果なので、#f とだけ区別する。
           (define pairs
             (and diff (substitution-pairs name (car diff) (cdr diff))))
           (cond
             [(not pairs) 'fail]
             [else
              (for/fold ([acc prov]) ([pair (in-list pairs)])
                (for/fold ([acc acc])
                          ([place (in-list
                                   (place-candidates (cdr pair)
                                                     known-places))])
                  (provenance-add acc (car pair) place)))])])]
       [else 'fail])]))

;; spec §4.6。Scope 内で place を確保する束縛は H の増分から fresh place を取る。
;; 増分がちょうど 1 件で、同じ place が Ω にも増えている場合だけ採る。
;; R-LetMutB も Scope ごと入れ替わり H へ place を 1 つ足すので、名前に
;; owned を含むがこの手続きを共用する。bmode は照合で捨てている。
(define (extend-let-owned prov pre-parts post-parts)
  (define pre-H (table-keys (second pre-parts)))
  (define post-H (table-keys (second post-parts)))
  (define pre-Ω (table-keys (third pre-parts)))
  (define post-Ω (table-keys (third post-parts)))
  (define added-H (set-subtract post-H pre-H))
  (define added-Ω (set-subtract post-Ω pre-Ω))
  (cond
    [(not (= (set-count added-H) 1)) 'fail]
    [(not (equal? added-H added-Ω)) 'fail]
    [else
     (define p-new (set-first added-H))
     (define diff (control-diff (first pre-parts) (first post-parts)))
     (match (and diff (car diff))
       [`(Let (,x ,_bmode ,_τ) ,_v ,_body) (provenance-add prov x p-new)]
       ;; R-LetOwnedB の redex は Scope ごと入れ替わるので、Let を内側から探す。
       [(? list? redex)
        (define found (find-let-binder redex))
        (if found (provenance-add prov found p-new) 'fail)]
       [_ 'fail])]))

(define (find-let-binder t)
  (match t
    [`(Let (,x ,_bmode ,_τ) ,_v ,_body) x]
    [(? list?) (for/or ([sub (in-list t)]) (find-let-binder sub))]
    [_ #f]))

;; spec §4.6。生成域が空洞化していないことを示す 6 つの非空カウンタ。
;; 生成した構文ではなく、型検査を通った項の到達可能な trace の上で数える。
(struct bcounters (shared mut reborrow proj scope-exit use)
  #:mutable #:transparent)

(define (make-bcounters)
  (bcounters 0 0 0 0 0 0))

(define (bump! counters field)
  (case field
    [(shared) (set-bcounters-shared! counters
                                     (add1 (bcounters-shared counters)))]
    [(mut) (set-bcounters-mut! counters (add1 (bcounters-mut counters)))]
    [(reborrow) (set-bcounters-reborrow!
                 counters (add1 (bcounters-reborrow counters)))]
    [(proj) (set-bcounters-proj! counters (add1 (bcounters-proj counters)))]
    [(scope-exit) (set-bcounters-scope-exit!
                   counters (add1 (bcounters-scope-exit counters)))]
    [(use) (set-bcounters-use! counters (add1 (bcounters-use counters)))]
    [else (error 'bump! "未知のカウンタ: ~s" field)]))

(define (bcounters-zeros c)
  (for/list ([pair (in-list (list (cons 'shared (bcounters-shared c))
                                  (cons 'mut (bcounters-mut c))
                                  (cons 'reborrow (bcounters-reborrow c))
                                  (cons 'proj (bcounters-proj c))
                                  (cons 'scope-exit (bcounters-scope-exit c))
                                  (cons 'use (bcounters-use c))))]
             #:when (zero? (cdr pair)))
    (car pair)))

;; spec §4.4。構成へ注入した BorrowAt の ρ は request の alpha を σ で解いた寿命である。
(define (static-borrow-set sidecar ir)
  (for/list ([req (in-list (borrow-sidecar-requests sidecar))])
    (define rho-borrow (borrow-request-rho-borrow req))
    (define alpha (borrow-request-alpha req))
    (define ρ
      (if (lifetime-var? alpha)
          (let ([solved
                 (hash-ref (borrow-sidecar-sigma sidecar)
                           (lifetime-var-index alpha))])
            (if ir (region->rho ir solved) solved))
          (if (and ir (region? rho-borrow))
              (region->rho ir rho-borrow)
              rho-borrow)))
    (list (borrow-request-mode req)
          (borrow-request-w req)
          (borrow-request-fp req)
          ρ)))

;; spec §4.5。制御項と H に現れる借用値だけを生存とみなす。
;; 借用値は (mode p fp ρ) の 4 つ組へ正規化する。
(define (normalize-borrow v)
  (match v
    [`(BorrowRef ,p ,fp ,ρ) (list 'shared p fp ρ)]
    [`(BorrowMutRef ,p ,fp ,ρ) (list 'mut p fp ρ)]))

(define (live-borrows config)
  (define parts (cfg-parts config))
  (and parts
       (map normalize-borrow
            (append (collect-borrow-values (first parts))
                    (collect-borrow-values (second parts))))))

;; θ の obs payload にしか現れない借用がある実行は捨てる。
(define (obs-only-borrow? config)
  (define parts (cfg-parts config))
  (and parts
       (let ([live (list->set (map normalize-borrow
                                   (append (collect-borrow-values
                                            (first parts))
                                           (collect-borrow-values
                                            (second parts)))))]
             [in-trace (map normalize-borrow
                            (collect-borrow-values (fifth parts)))])
         (for/or ([b (in-list in-trace)]) (not (set-member? live b))))))

;; 同じ place で、一方の欄 path が他方の接頭辞であるとき重なるとみなす。
(define (borrows-overlap? a b)
  (and (equal? (second a) (second b))
       (let ([fa (third a)] [fb (third b)])
         (or (prefix-of? fa fb) (prefix-of? fb fa)))))

(define (prefix-of? short long)
  (and (<= (length short) (length long))
       (equal? short (take long (length short)))))

;; 条件 1。生きている借用の place を move も drop もしない。
;; Ω が Available から Moved か Dropped へ変わった place を見る。
(define (check-no-move-of-live pre post)
  (define pre-parts (cfg-parts pre))
  (define post-parts (cfg-parts post))
  (define live (live-borrows pre))
  (define invalidated
    (for/list ([entry (in-list (third post-parts))]
               #:when (and (memq (second entry) '(Moved Dropped))
                           (equal? (assoc (first entry) (third pre-parts))
                                   (list (first entry) 'Available))))
      (first entry)))
  (for/or ([p (in-list invalidated)])
    (and (for/or ([b (in-list live)]) (equal? (second b) p))
         (list 'fail 'move-of-live-borrow p))))

;; 条件 2。可変借用が他の借用と重なって同時に生きていない。
;; 同じ正規化借用の複数の出現は、取得ではなく同じ loan の複製である。
(define (parent-edge-pair edge)
  (match edge
    [(list 'derived child parent) (list child parent)]
    [(list 'reborrow child parent) (list child parent)]
    [(list child parent) (list child parent)]
    [_ #f]))

(define (loan-ancestor? descendant ancestor edges)
  (let loop ([pending (list descendant)] [seen (set)])
    (match pending
      ['() #f]
      [(cons loan rest)
       (cond
         [(equal? loan ancestor) #t]
         [(set-member? seen loan) (loop rest seen)]
         [else
          (define parents
            (for/list ([edge (in-list edges)]
                       #:when (equal? (first edge) loan))
              (second edge)))
          (loop (append rest parents) (set-add seen loan))])])))

(define (check-mut-exclusive config [parent-edges '()])
  (define live (live-borrows config))
  (define edges (filter values (map parent-edge-pair parent-edges)))
  (define (related? a b)
    (or (loan-ancestor? a b edges) (loan-ancestor? b a edges)))
  (for*/or ([a (in-list live)]
            [b (in-list live)]
            #:unless (equal? a b))
    (and (borrows-overlap? a b)
         (or (eq? (first a) 'mut) (eq? (first b) 'mut))
         (not (related? a b))
         (list 'fail 'mut-not-exclusive (list a b)))))

;; 条件 3。reborrow の子が生きている間、親の可変借用は現れない。
(define (check-reborrow-parents config parents)
  (define live (list->set (live-borrows config)))
  (define projection-children
    (for/set ([edge (in-list parents)]
              #:when (match edge [(list 'derived _ _) #t] [_ #f]))
      (second edge)))
  (for/or ([edge (in-list parents)])
    (match edge
      [(list 'reborrow child parent)
       ;; 射影からの再借用では、parent の後続出現だけで拒否しない。
       ;; 実際に親を消費した step は derived-parent-use-failure で判定する。
       (and (not (set-member? projection-children parent))
            (set-member? live child)
            (set-member? live parent)
            (list 'fail 'reborrow-parent-live (list child parent)))]
      [(list child parent)
       (and (set-member? live child)
            (set-member? live parent)
            (list 'fail 'reborrow-parent-live edge))]
      [_ #f])))

;; R-BorrowMut の step 前に同じ可変 loan が生きていれば、別取得として拒否する。
(define (reacquired-live-mut name candidates pre)
  (and (eq? name 'R-BorrowMut)
       (let ([live (live-borrows pre)])
         (for/or ([candidate (in-list candidates)])
           (match candidate
             [(list 'root 'mut p fp ρ _w)
              (define b (list 'mut p fp ρ))
              (and (member b live)
                   (list 'fail 'mut-not-exclusive (list b b)))]
             [_ #f])))))

;; 親は出現しているだけでは停止違反にならないが、子の生存中に消費はできない。
(define (derived-parent-use-failure candidates pre parents)
  (define live (list->set (live-borrows pre)))
  (define edges (filter values (map parent-edge-pair parents)))
  (define (source candidate)
    (match candidate
      [(list 'use 'mut p fp ρ)
       (list (list 'mut p fp ρ) (list 'mut p fp ρ))]
      [(list 'derived _mode p fp _ρ pp pfp pρ)
       (list (list 'mut pp pfp pρ) (list 'mut p fp pρ))]
      [(list 'reborrow p fp _ρ ρ-parent)
       (list (list 'mut p fp ρ-parent) (list 'mut p fp ρ-parent))]
      [_ #f]))
  (for/or ([candidate (in-list candidates)])
    (define source-pair (source candidate))
    (define parent (and source-pair (first source-pair)))
    (define operation (and source-pair (second source-pair)))
    (and parent
         (set-member? live parent)
         (for/or ([edge (in-list edges)])
           (define child (first edge))
           (and (not (equal? child parent))
                (set-member? live child)
                (loan-ancestor? child parent edges)
                (borrows-overlap? child operation)
                (list 'fail 'reborrow-parent-live (list child parent)))))))

;; spec §4.6。static request の designator が動的な place へ解けるかを調べる。
;; 解が無いときは #f、全てが p のときは #t、複数の place へ散るときは
;; ambiguous を返す。複数 request の結果は static-match-verdict でまとめる。
(define (designator-status prov w p)
  (define places (resolve-designator prov w))
  (cond
    [(null? places) #f]
    [(andmap (lambda (place) (equal? place p)) places) #t]
    [else (list 'ambiguous places)]))

;; 同じ mode、fp、ρ の request が複数ある場合も順序に依存させない。
;; 一つでも一意に一致すれば受理し、受理が無く ambiguous があれば fail にする。
(define (static-match-verdict statics mode fp ρ p prov)
  (define matched? #f)
  (define ambiguous-detail #f)
  (for ([entry (in-list statics)])
    (match-define (list s-mode s-w s-fp s-ρ) entry)
    (when (and (eq? mode s-mode)
               (equal? fp s-fp)
               (equal? ρ s-ρ))
      (define status (designator-status prov s-w p))
      (cond
        [(eq? status #t) (set! matched? #t)]
        [(and (pair? status) (eq? (first status) 'ambiguous)
              (not ambiguous-detail))
         (set! ambiguous-detail
               (list 'static entry 'dynamic-place p
                     'places (second status)))])))
  (cond
    [matched? #t]
    [ambiguous-detail (list 'fail 'ambiguous-designator ambiguous-detail)]
    [else #f]))

;; spec §4.6。根の発生は静的側の要求と mode と fp と ρ で照合する。
;; 個数の一致は要求しない。R-RecurUnfold の複製で同じ要求が複数回発火しうる。
(define (root-matches? candidate statics prov)
  (match-define (list _tag mode p fp ρ _w) candidate)
  (static-match-verdict statics mode fp ρ p prov))

;; reborrow は根でありながら親を持つ。静的側との照合は根と同じ規則で、
;; 親の可変借用が簡約前に生きていることも要求する。
(define (reborrow-matches? candidate statics prov pre)
  (match-define (list _tag p fp ρ ρ-parent) candidate)
  (define parent (list 'mut p fp ρ-parent))
  (and (member parent (live-borrows pre))
       (static-match-verdict statics 'shared fp ρ p prov)))

;; 派生の発生は親の参照とだけ照合する。静的側は見ない。
;; 形の妥当性は Task 2 の approved-forms が既に確かめている。
(define (derived-matches? candidate pre)
  (match-define (list _tag _mode _p _fp _ρ p-parent fp-parent ρ-parent)
    candidate)
  (for/or ([b (in-list (live-borrows pre))])
    (and (equal? (second b) p-parent)
         (equal? (third b) fp-parent)
         (equal? (fourth b) ρ-parent))))

;; spec §4.5。1 本の実行を歩き、三条件と発生の照合を課す。
;; 返り値は 'ok か 'discard か (list 'fail reason detail) である。
(define (check-borrow-execution config sidecar ir fuel counters)
  (define statics (if sidecar (static-borrow-set sidecar ir) '()))
  (let loop ([current config]
             [prov (empty-provenance)]
             [parents '()]
             [remaining fuel]
             [scopes (count-scopes config)])
    (cond
      [(obs-only-borrow? current) 'discard]
      ;; 条件 3 を条件 2 より先に見る。reborrow の子と親は place も欄 path も
      ;; 同じなので通常の直接の reborrow では従来の診断順を保つ。
      [(check-reborrow-parents current parents) => values]
      [(check-mut-exclusive current parents) => values]
      [(zero? remaining) 'discard]
      [else
       (define steps (raw-steps-g2/named current))
       (cond
         [(null? steps) 'ok]
         [(> (length steps) 1) (list 'fail 'nondeterministic steps)]
         [else
          (match-define (list name next) (first steps))
          (define next-prov (provenance-extend prov name current next))
          (cond
            [(eq? next-prov 'fail) (list 'fail 'provenance name)]
            [(check-no-move-of-live current next) => values]
            [else
             (define diff (control-diff (first (cfg-parts current))
                                        (first (cfg-parts next))))
             (define raw-candidates
               (if diff
                   (borrow-form-candidates (car diff) (cdr diff)
                                           #:rule name)
                   '()))
             ;; 置換規則は借用値を本体へ運ぶことがある。ここで既知の
             ;; 置換を未検証の借用生成として扱わず、実際の発生だけを
             ;; approved-forms で分類する。
             (define candidates
               (if (and (equal? raw-candidates (list (list 'unverified)))
                        (eq? (rule-bucket name) 'substituting))
                   '()
                   raw-candidates))
             (cond
               [(reacquired-live-mut name candidates current) => values]
               [(for/or ([candidate (in-list candidates)])
                  (equal? candidate (list 'unverified)))
                (list 'fail 'unverified-borrow-form diff)]
               [else
                (define verdict
                  (and (pair? candidates)
                       (classify-all! candidates statics next-prov
                                      current counters)))
                (cond
                  [(and verdict (eq? (first verdict) 'fail)) verdict]
                  [(derived-parent-use-failure candidates current parents) => values]
                  [else
                   (define next-scopes (count-scopes next))
                   (when (and (< next-scopes scopes)
                              (positive? next-scopes)
                              (borrow-survives? current next))
                     (bump! counters 'scope-exit))
                   (loop next next-prov
                         (for/fold ([updated parents])
                                   ([candidate (in-list candidates)])
                           (update-parents updated candidate current))
                         (sub1 remaining) next-scopes)])])])])])))

;; 候補を分類し、照合してカウンタを進める。fail なら理由を返す。
(define (classify! candidate statics prov pre counters)
  (match candidate
    [(list 'root mode _p _fp _ρ _w)
     (define matched (root-matches? candidate statics prov))
     (cond
       [(and (pair? matched) (eq? (first matched) 'fail)) matched]
       [matched (begin (bump! counters (if (eq? mode 'mut) 'mut 'shared)) #f)]
       [else (list 'fail 'unmatched-root candidate)])]
    [(list 'reborrow _p _fp _ρ _ρ-parent)
     (define matched (reborrow-matches? candidate statics prov pre))
     (cond
       [(and (pair? matched) (eq? (first matched) 'fail)) matched]
       [matched (begin (bump! counters 'reborrow) #f)]
       [else (list 'fail 'unmatched-reborrow candidate)])]
    [(list 'derived _mode _p _fp _ρ _pp _pfp _pρ)
     (if (derived-matches? candidate pre)
         (begin (bump! counters 'proj) #f)
         (list 'fail 'unmatched-derived candidate))]
    [(list 'use _mode _p _fp _ρ) (bump! counters 'use) #f]
    [_ (list 'fail 'unknown-candidate candidate)]))

(define (classify-all! candidates statics prov pre counters)
  (for/or ([candidate (in-list candidates)])
    (classify! candidate statics prov pre counters)))

;; 内側 Scope の退出だけを数えるため、退出後も Scope が残っている遷移に限る。
;; 最外の Scope の退出は次の Scope 数が 0 になるので数えない。
(define (count-scopes t)
  (cond [(and (pair? t) (eq? (first t) 'Scope))
         (add1 (for/sum ([sub (in-list (rest t))]) (count-scopes sub)))]
        [(list? t) (for/sum ([sub (in-list t)]) (count-scopes sub))]
        [else 0]))

;; Scope が 1 つ減った遷移で、簡約前に生きていた借用が簡約後も生きているか。
(define (borrow-survives? pre post)
  (define before (live-borrows pre))
  (define after (list->set (live-borrows post)))
  (for/or ([b (in-list before)]) (set-member? after b)))

(define (update-parents parents candidate pre)
  (match candidate
    [(list 'reborrow p fp ρ ρ-parent)
     (cons (list 'reborrow
                 (list 'shared p fp ρ)
                 (list 'mut p fp ρ-parent))
           parents)]
    [(list 'derived mode p fp ρ pp pfp pρ)
     (append
      (for/list ([parent (in-list (live-borrows pre))]
                 #:when (and (equal? (second parent) pp)
                             (equal? (third parent) pfp)
                             (equal? (fourth parent) pρ)))
        (list 'derived (list mode p fp ρ) parent))
      parents)]
    [_ parents]))
