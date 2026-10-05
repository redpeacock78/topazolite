#lang racket

(require racket/match
         racket/set
         "data-env.rkt"
         "erase.rkt"
         "rows.rkt"
         "schema.rkt"
         "type-equiv.rkt"
         "validators.rkt")

(provide type-shape-ok?
         owned-union-member?
         core-types-normal?
         proposition-shape-ok?
         proposition-types-normal?
         effect-row-normal?
         storage-ok?
         type-carries-capability?
         proj-borrow-mode)

;; spec §5.2。親の mode と field の可変性から子の mode を決める。
;; capability が BorrowedMut であることは path 上の全 field が mut である
;; ことを含意するため、後段で path 全体を再検査しない。
(define (proj-borrow-mode m_parent m_field)
  (if (and (eq? m_parent 'BorrowedMut) (eq? m_field 'mut))
      'BorrowedMut
      'Borrowed))

;; 型が Borrowed または BorrowedMut を含むか。Eliminate の branch binder へ
;; 所有者を運べない段で fail-closed にするために使う。
(define (type-carries-capability? type)
  (let walk ([type type] [visited (set)])
    (match type
      [`(Borrowed ,_ ,_) #t]
      [`(BorrowedMut ,_ ,_) #t]
      [`(Data ,name (,arguments ...))
       (define key (cons name arguments))
       (define schema (data-schema name arguments))
       (cond
         [(not schema) #t]
         [(set-member? visited key) #f]
         [else
          (for/or ([field (in-list (data-field-types name arguments))])
            (walk field (set-add visited key)))])]
      [(? list? terms) (ormap (lambda (term) (walk term visited)) terms)]
      [_ #f])))

(define (proposition-shape-ok? proposition)
  (match proposition
    [`(Implements ,type ,_) (type-shape-ok? type)]
    [`(FieldType ,_ ,type) (type-shape-ok? type)]
    [`(RemainderSafelyDropped ,actual ,expected)
     (and (type-shape-ok? actual) (type-shape-ok? expected))]
    ;; unsafe.md §5.1。識別子の許可集合をここで閉じる。既定の #t へ落とすと
    ;; Proof と Q と Refined の内側で許可集合の外の識別子が通る。
    [`(PtrProp ,id ,type)
     (and (ptr-prop-id-ok? id) (type-shape-ok? type))]
    [_ #t]))

(define (effect-row-shape-ok? row)
  (for/and ([label (in-list row)])
    (match label
      [`(Return ,_ ,type) (type-shape-ok? type)]
      [`(Yield ,type) (type-shape-ok? type)]
      [_ #t])))

;; 再帰する data schema の形検査で、同じ具体化を再訪したか記録する。
(define data-shape-visited (make-parameter (set)))

;; 型の整形式性。record のラベル一意性に加えて、RFN-001 の Owned-free 制限を
;; Untrusted と Refined のペイロードへ課す。
(define (type-shape-ok? type)
  (check-spanless! 'type-shape-ok? type)
  (match type
    [`(Record ,row)
     (and (field-row-unique? row)
          (for/and ([field (in-list row)])
            (type-shape-ok? (second field))))]
    [`(List ,element) (type-shape-ok? element)]
    [`(Option ,element) (type-shape-ok? element)]
    [`(Result ,ok-type ,error-type)
     (and (type-shape-ok? ok-type)
          (type-shape-ok? error-type))]
    ;; unsafe.md §3.4。Owned の直下に raw pointer を置けない。pointer 値が
    ;; Owned の境界を越えると、typing.rkt の heap 値の再検査が
    ;; PtrVal を所有の木の節点として扱わなければならなくなる。
    [`(Owned (RawPtr ,_ ,_ ,_ ,_ ,_ ,_)) #f]
    [`(Owned ,inner) (type-shape-ok? inner)]
    ;; 借用は所有ではないため、payload を Owned で包めない。
    ;; 禁じるのは直接の Owned だけである。Untrusted と Refined が使う再帰的な
    ;; owned-free? は採らない。所有値を含む構造の借用は意図された用法である
    ;; （ホワイトペーパー 709 行の borrowed view）。
    [`(Borrowed (Owned ,_) ,_) #f]
    [`(BorrowedMut (Owned ,_) ,_) #f]
    [`(Borrowed ,inner ,_) (type-shape-ok? inner)]
    [`(BorrowedMut ,inner ,_) (type-shape-ok? inner)]
    [`(RawPtr ,payload ,_ ,_ ,_ ,_ ,_)
     (and (raw-ptr-components-ok? type) (type-shape-ok? payload))]
    [`(Untrusted ,inner)
     (and (owned-free? inner) (type-shape-ok? inner))]
    [`(Refined ,inner ,proposition)
     (and (owned-free? inner)
          (type-shape-ok? inner)
          (proposition-shape-ok? proposition))]
    [`(Union ,left ,right)
     (and (not (match left [`(Owned ,_) #t] [_ #f]))
          (not (match right [`(Owned ,_) #t] [_ #f]))
          (type-shape-ok? left)
          (type-shape-ok? right))]
    [`(Intersection ,left ,right)
     (and (type-shape-ok? left) (type-shape-ok? right))]
    [`(Proof ,proposition)
     (proposition-shape-ok? proposition)]
    [`(NFn ,parameters ,return-type ,in-row ,out-row ,obligations ,_origin)
     (and (andmap type-shape-ok? parameters)
          (type-shape-ok? return-type)
          (effect-row-shape-ok? in-row)
          (effect-row-shape-ok? out-row)
          (andmap proposition-shape-ok? obligations))]
    [`(ForallRegion (,_ ...) ,body) (type-shape-ok? body)]
    [`(Data ,name (,arguments ...))
     (define key (cons name arguments))
     (define schema (data-schema name arguments))
     (and schema
          (andmap type-shape-ok? arguments)
          (or (set-member? (data-shape-visited) key)
              (parameterize ([data-shape-visited
                              (set-add (data-shape-visited) key)])
                (for*/and ([row (in-list schema)]
                           [field (in-list (second row))])
                  (type-shape-ok? field)))))]
    [_ #t]))

;; PAT-001。Owned は Union の直下の成分に置けない。
;; Data の欄に現れる Union も同じ制約で調べる。
(define (owned-union-member? subject)
  (let walk ([type subject] [visited (set)])
    (match type
      [`(Union ,left ,right)
       (or (ormap (lambda (member)
                    (match member [`(Owned ,_) #t] [_ #f]))
                  (union-members type))
           (walk left visited)
           (walk right visited))]
      [`(Data ,name (,arguments ...))
       (define key (cons name arguments))
       (define schema (data-schema name arguments))
       (or (ormap (lambda (argument) (walk argument visited)) arguments)
           (and schema
                (not (set-member? visited key))
                (for/or ([field (in-list (data-field-types name arguments))])
                  (walk field (set-add visited key)))))]
      [(? list? terms) (ormap (lambda (term) (walk term visited)) terms)]
      [_ #f])))

;; 可変記憶域の書込み先の型が、value path で到達するすべての NFn に
;; Partial を持たせているかを判定する（REC-001、P2i3 spec §3.2）。
;; NFn の仮引数型、戻り型、Q へは降りない。Proof と TypeInfo は callable を
;; 運ばないので辿らない。data schema と組み込み List/Option/Result の欄を辿る。
(define (storage-ok? τ-in)
  (define (schema-key τ)
    (match τ
      [`(Data ,name (,arguments ...)) (cons name arguments)]
      [`(List ,element) (list 'List element)]
      [`(Option ,element) (list 'Option element)]
      [`(Result ,ok-type ,error-type) (list 'Result ok-type error-type)]))
  (let walk ([τ-in τ-in] [visited (set)])
    (define τ (normalize-type τ-in))
    (match τ
      [#f #f]
      [(or 'Int 'Bool 'Unit 'String 'Never 'Res) #t]
      [`(TypeInfo ,_) #t]
      [`(Proof ,_) #t]
      [`(NFn ,_ ,_ ,_ ,εout ,_ ,_) (and (member 'Partial εout) #t)]
      [`(Record ,row)
       (for/and ([field (in-list row)]) (walk (second field) visited))]
      [`(Union ,a ,b) (and (walk a visited) (walk b visited))]
      [(or `(Data ,_ (,_ ...)) `(List ,_) `(Option ,_) `(Result ,_ ,_))
       (define key (schema-key τ))
       (define schema (constructor-schema τ))
       (and schema
            (or (set-member? visited key)
                (for*/and ([constructor (in-list schema)]
                           [field (in-list (second constructor))])
                  (walk field (set-add visited key)))))]
      [`(Owned ,a) (walk a visited)]
      [`(Borrowed ,a ,_) (walk a visited)]
      [`(BorrowedMut ,a ,_) (walk a visited)]
      [`(Untrusted ,a) (walk a visited)]
      [`(Refined ,a ,_) (walk a visited)]
      [`(ForallRegion ,_ ,a) (walk a visited)]
      [`(RawPtr ,a ,_ ,_ ,_ ,_ ,_) (walk a visited)]
      [_ #f])))

;; 命題に埋め込まれた型が全て正規形か。
(define (proposition-types-normal? proposition)
  (and (equal? (normalize-proposition proposition) proposition)
       (match proposition
         [`(Implements ,type ,_) (type-normal? type)]
         [`(FieldType ,_ ,type) (type-normal? type)]
         [`(RemainderSafelyDropped ,actual ,expected)
          (and (type-normal? actual) (type-normal? expected))]
         [_ #t])))

;; 作用列の Return/Yield に埋め込まれた型が全て正規形か。
(define (effect-row-normal? row)
  (for/and ([label (in-list row)])
    (match label
      [`(Return ,_ ,type) (type-normal? type)]
      [`(Yield ,type) (type-normal? type)]
      [_ #t])))

;; Core 項と設定に現れる全ての型保持位置を明示的に走査する。
(define (core-types-normal? subject)
  (define (walk-origin origin)
    (match origin
      ['User #t]
      [`(Reserved ,_) #t]
      [`(Derived ,parent ,step)
       (and (walk-origin parent) (walk-step step))]
      [_ (error 'core-types-normal? "unhandled origin form: ~s" origin)]))

  (define (walk-step step)
    (match step
      [`(Curry ,value) (walk value)]
      [`(Make ,type) (type-normal? type)]
      [`(Expand ,_) #t]
      ;; NAR-003: core-types-normal? が閉じるのは到達可能な Trait である。
      [`(Trait ,_) #t]
      ;; NAR-004: Γ0 の impl/intersect origin は Policy TraitResolution を
      ;; 親に持ち、typing の configuration へ到達するため、型欄のない Policy
      ;; を受理する。Compose は合成 Implements の Proof 値を書き下す正典構文が
      ;; まだ無く core の値として構築できないため、ここでは受理しない。
      [`(Policy ,_) #t]
      ;; NAR-004: Impl は第 3 欄に対象型を持つため、Make と同じく辿る。
      ;; Intersect は trait 名しか持たないため受理する。
      [`(Impl ,_ ,_ ,type ,_) (type-normal? type)]
      [`(Intersect ,_ ,_ ,_ ,_) #t]
      [_ (error 'core-types-normal? "unhandled origin step: ~s" step)]))

  (define (walk-branch branch)
    (match branch
      [`(,_ (,_ ...) -> ,body) (walk body)]
      [_ (error 'core-types-normal? "unhandled branch form: ~s" branch)]))

  (define (walk-ubr branch)
    (match branch
      [`(,type ,_ -> ,body) (and (type-normal? type) (walk body))]
      [_ (error 'core-types-normal? "unhandled ubr form: ~s" branch)]))

  (define (walk-record-field field)
    (match field
      [`(,_ ,_ ,core) (walk core)]
      [_ (error 'core-types-normal? "unhandled record field: ~s" field)]))

  (define (walk-heap-entry entry)
    (match entry
      [`(,_ ,value) (walk value)]
      [`(,_ ,value (declared ,type))
       (and (type-normal? type) (walk value))]
      [_ (error 'core-types-normal? "unhandled heap entry: ~s" entry)]))

  (define (walk-event event)
    (match event
      [`(obs ,value) (walk value)]
      [`(fin ,_) #t]
      [`(finLeaf ,_ ,_) #t]
      [_ (error 'core-types-normal? "unhandled event form: ~s" event)]))

  (define (walk value)
    (cond
      [(or (exact-integer? value) (string? value) (symbol? value)) #t]
      [else
       (match value
         [`(cfg ,core ,heap ,_states ,_tokens ,events)
          (and (walk core)
               (andmap walk-heap-entry heap)
               (andmap walk-event events))]
         [`(Apply ,function ,arguments ...)
          (and (walk function) (andmap walk arguments))]
         [`(Let (,_ ,_ ,type) ,bound ,body)
          (and (type-normal? type) (walk bound) (walk body))]
         [`(Let (,_ ,type) ,bound ,body)
          (and (type-normal? type) (walk bound) (walk body))]
         [`(Construct ,type ,_ ,fields ...)
          (and (type-normal? type) (andmap walk fields))]
         [`(UnionInject ,union-type ,member-type ,payload)
          (and (normalize-type union-type)
               (normalize-type member-type)
               (walk payload))]
         [`(UnionEliminate ,scrutinee ,branches)
          (and (walk scrutinee) (andmap walk-ubr branches))]
         [`(Eliminate ,scrutinee ,branches)
          (and (walk scrutinee) (andmap walk-branch branches))]
         [`(Perform (Return ,_ ,type) ,argument)
          (and (type-normal? type) (walk argument))]
         [`(Handle (Return ,_ ,type) (,_ -> ,handler-body) ,body)
          (and (type-normal? type) (walk handler-body) (walk body))]
         [`(Scope ,_ ,body) (walk body)]
         [`(Recur ,_ ,_ (,_ ...) ,body ,continuation)
          (and (walk body) (walk continuation))]
         [`(Yield ,observed ,next)
          (and (walk observed) (walk next))]
         [`(Suspend ,body) (walk body)]
         ;; 借用の 8 形。型を持つ位置が無いため、operand を辿るだけでよい。
         ;; w は designator、ρ は region 識別子、p は place であり、
         ;; いずれも型ではない。
         [`(Borrow ,_) #t]
         [`(BorrowMut ,_) #t]
         [`(BorrowAt ,_ ,_ ,_) #t]
         [`(BorrowMutAt ,_ ,_ ,_) #t]
         [`(BorrowRef ,_ ,_ ,_) #t]
         [`(BorrowMutRef ,_ ,_ ,_) #t]
         [`(Reborrow ,operand) (walk operand)]
         [`(ReborrowAt ,_ ,_ ,operand) (walk operand)]
         [`(ProjBorrow ,operand ,_) (walk operand)]
         [`(ProjBorrowAt ,_ ,_ ,operand ,_) (walk operand)]
         [`(Read ,operand) (walk operand)]
         [`(Assign ,target ,value) (and (walk target) (walk value))]
         [`(Reassign ,target ,value) (and (walk target) (walk value))]
         [`(RegionLam (,_ ...) ,body) (walk body)]
         [`(RegionApp ,function (,_ ...)) (walk function)]
         ;; pointer 操作（unsafe.md §4.4）。型を持つ位置が無いため operand を
         ;; 辿るだけでよい。ρ は region 識別子、p と fp と ptrmut と prov は
         ;; 型ではない。
         [`(AddressOf ,operand) (walk operand)]
         [`(RawLoad ,operand) (walk operand)]
         [`(Unsafe ,body) (walk body)]
         [`(PtrOffset ,operand ,offset)
          (and (walk operand) (walk offset))]
         [`(RawStore ,target ,value)
          (and (walk target) (walk value))]
         [`(FromRawPtr ,operand ,_) (walk operand)]
         [`(PtrVal ,_ ,_ ,_ ,_) #t]
         [`(Move ,_) #t]
         [`(MutSlot ,_) #t]
         [`(Absent ,type) (type-normal? type)]
         [`(Drop ,argument) (walk argument)]
         [`(Curry ,function ,argument)
          (and (walk function) (walk argument))]
         [`(Error ,_) #t]
         [`(Rec ,fields) (andmap walk-record-field fields)]
         [`(RecRewrite ,input ,entries)
          (and (walk input)
               (for/and ([entry (in-list entries)])
                 (match entry
                   [`(,_ ,_ ,input-type ,_ ,output-type ,body)
                    (and (type-normal? input-type)
                         (type-normal? output-type)
                         (walk body))]
                   [_ #f])))]
         [`(Proj ,record ,_) (walk record)]
         [`(ProjOpt ,type ,record ,_)
          (and (type-normal? type) (walk record))]
         [`(resource ,_) #t]
         [`(OwnLeaf ,payload) (walk payload)]
         [`(OwnedLeaf ,_ ,payload) (walk payload)]
         [`(UnionVal ,union-type ,member-type ,payload)
          (and (type-normal? union-type)
               (type-normal? member-type)
               (walk payload))]
         [`(UVal ,payload) (walk payload)]
         [`(RVal ,proof ,payload) (and (walk proof) (walk payload))]
         ;; PRF-004: 搬送された ProofRep は core に現れる。包み先と Proof の
         ;; どちらも通常の core として辿る。
         [`(Discharge ,proof ,inner) (and (walk proof) (walk inner))]
         [`(Lam ,origin ,_ (,_ ...) ,body)
          (and (walk-origin origin) (walk body))]
         [`(PrimVal ,origin ,_) (walk-origin origin)]
         [`(CurryVal ,origin ,function ,argument)
          (and (walk-origin origin) (walk function) (walk argument))]
         [`(RecurVal ,_ ,_ (,_ ...) ,body) (walk body)]
         [`(TypeRep ,origin ,type ,_)
          (and (walk-origin origin) (type-normal? type))]
         [`(ProofRep ,origin ,proposition)
          (and (walk-origin origin)
               (proposition-types-normal? proposition))]
         [_ (error 'core-types-normal? "unhandled core form: ~s" value)])]))

  ;; spanful な項は投影してから走査する。span.md §7 の通り type-shape は項を
  ;; 走査するが span を見ない判定であり、判定結果に位置情報を持たない。
  ;; 投影は spanless な入力では恒等写像であり、知らない metadata head では error を
  ;; 上げる。keyword でない未知の構成子は従来どおり walk の unhandled 節で落ちる。
  (walk (erase-core subject)))
