#lang racket

(require racket/match
         "erase.rkt"
         "rows.rkt"
         "type-equiv.rkt"
         "validators.rkt")

(provide type-shape-ok?
         core-types-normal?
         proposition-types-normal?
         effect-row-normal?
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
  (match type
    [`(Borrowed ,_ ,_) #t]
    [`(BorrowedMut ,_ ,_) #t]
    [(? list? terms) (ormap type-carries-capability? terms)]
    [_ #f]))

(define (proposition-shape-ok? proposition)
  (match proposition
    [`(Implements ,type ,_) (type-shape-ok? type)]
    [`(FieldType ,_ ,type) (type-shape-ok? type)]
    [_ #t]))

(define (effect-row-shape-ok? row)
  (for/and ([label (in-list row)])
    (match label
      [`(Return ,_ ,type) (type-shape-ok? type)]
      [`(Yield ,type) (type-shape-ok? type)]
      [_ #t])))

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
    [`(Owned ,inner) (type-shape-ok? inner)]
    ;; 借用は所有ではないため、payload を Owned で包めない。
    ;; 禁じるのは直接の Owned だけである。Untrusted と Refined が使う再帰的な
    ;; owned-free? は採らない。所有値を含む構造の借用は意図された用法である
    ;; （ホワイトペーパー 709 行の borrowed view）。
    [`(Borrowed (Owned ,_) ,_) #f]
    [`(BorrowedMut (Owned ,_) ,_) #f]
    [`(Borrowed ,inner ,_) (type-shape-ok? inner)]
    [`(BorrowedMut ,inner ,_) (type-shape-ok? inner)]
    [`(Untrusted ,inner)
     (and (owned-free? inner) (type-shape-ok? inner))]
    [`(Refined ,inner ,proposition)
     (and (owned-free? inner)
          (type-shape-ok? inner)
          (proposition-shape-ok? proposition))]
    [`(Union ,left ,right)
     (and (type-shape-ok? left) (type-shape-ok? right))]
    [`(Intersection ,left ,right)
     (and (type-shape-ok? left) (type-shape-ok? right))]
    [`(Proof ,proposition)
     (proposition-shape-ok? proposition)]
    [`(NFn ,parameters ,return-type ,row ,obligations)
     (and (andmap type-shape-ok? parameters)
          (type-shape-ok? return-type)
          (effect-row-shape-ok? row)
          (andmap proposition-shape-ok? obligations))]
    [_ #t]))

;; 命題に埋め込まれた型が全て正規形か。
(define (proposition-types-normal? proposition)
  (and (equal? (normalize-proposition proposition) proposition)
       (match proposition
         [`(Implements ,type ,_) (type-normal? type)]
         [`(FieldType ,_ ,type) (type-normal? type)]
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
      [_ (error 'core-types-normal? "unhandled origin step: ~s" step)]))

  (define (walk-branch branch)
    (match branch
      [`(,_ (,_ ...) -> ,body) (walk body)]
      [_ (error 'core-types-normal? "unhandled branch form: ~s" branch)]))

  (define (walk-record-field field)
    (match field
      [`(,_ ,_ ,core) (walk core)]
      [_ (error 'core-types-normal? "unhandled record field: ~s" field)]))

  (define (walk-heap-entry entry)
    (match entry
      [`(,_ ,value) (walk value)]
      [_ (error 'core-types-normal? "unhandled heap entry: ~s" entry)]))

  (define (walk-event event)
    (match event
      [`(obs ,value) (walk value)]
      [`(fin ,_) #t]
      [_ (error 'core-types-normal? "unhandled event form: ~s" event)]))

  (define (walk value)
    (cond
      [(or (exact-integer? value) (string? value) (symbol? value)) #t]
      [else
       (match value
         [`(cfg ,core ,heap ,_ ,events)
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
         [`(Move ,_) #t]
         [`(Drop ,argument) (walk argument)]
         [`(Curry ,function ,argument)
          (and (walk function) (walk argument))]
         [`(Error ,_) #t]
         [`(Rec ,fields) (andmap walk-record-field fields)]
         [`(Proj ,record ,_) (walk record)]
         [`(resource ,_) #t]
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
