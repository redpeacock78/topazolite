#lang racket

(require racket/set
         rackunit
         redex/reduction-semantics
         "../backend-matrix.rkt"
         "../diagnostic.rkt"
         "../erase.rkt"
         "../lang.rkt"
         "../lowering.rkt"
         "../obs.rkt"
         "../origins.rkt"
         "../pr-lang.rkt"
         "../pr-machine.rkt"
         "../pr-obs.rkt")

;; [REQ: BAK-001] lowering 関係と符号化（backend-matrix.md §5）
;; [REQ: DIA-001] lowering の Diagnostic 生成（diagnostic.md §7、§12）

(define depth 5)
(define fuel 10000)

;; lower の 2 値を 1 つへ畳む。status を確かめてから写しを返す。
(define (lower-ok core)
  (define-values (status result) (lower core 'racket-cs))
  (check-eq? status 'ok (format "lower: ~s" result))
  result)

(define (lower-value-ok value)
  (define-values (status result) (lower-value value 'racket-cs))
  (check-eq? status 'ok (format "lower-value: ~s" result))
  result)

(define (lower-diagnostic core)
  (define-values (status result) (lower core 'racket-cs))
  (check-eq? status 'capability (format "lower: ~s" result))
  result)

;;; backend-matrix.md §5 の符号化

;; PR の literal と、: を含む記号を入れる（backend-matrix.md §7）。
;; fin と obs と unit は G2m の literal でもあり源の名前になれないので、
;; 衝突の対象から外す。
(define collision-names '(PLet return yield drop curry |a:b|))

(test-case
 "the five symbol encoders never collide with each other"
 (for ([name (in-list collision-names)])
   (define images
     (list (var-code name) (tag-code name) (label-code name)
           (boundary-code name) (shim name)))
   (check-equal? (length images) (set-count (list->set images))
                 (format "images of ~a" name))))

(test-case
 "each encoded name is accepted where PR expects it"
 ;; 素の名前が PR の literal と衝突する位置でも、符号化した名前は通る。
 (for ([name (in-list collision-names)])
   (check-true (redex-match? PR px (var-code name)) (format "px ~a" name))
   (check-true (redex-match? PR K (tag-code name)) (format "K ~a" name))
   (check-true (redex-match? PR label (label-code name)) (format "label ~a" name))
   (check-true (redex-match? PR pnm (boundary-code name)) (format "b ~a" name))
   (check-true (redex-match? PR pnm (shim name)) (format "tz ~a" name))))

;; lang.rkt の τ の全形から作る。入れ子と、型同値だが構文が違う組を含める。
(define type-fixtures
  '(Int Bool Unit String Never Res
    (List Int) (List Bool) (List (List Int))
    (Option Int) (Option (List Int))
    (Result Int String) (Result String Int)
    (Owned Res) (Owned Int)
    (NFn (Int) Int () ())
    (NFn ((List Int)) Int () ())
    (NFn ((Option Int)) Int () ())
    (NFn (Int Int) Int () ())
    (NFn (Int) Int ((Return io Int)) ())
    (NFn (Int) Int () (TypeNarrativeCap))
    (TypeInfo Type) (TypeInfo (Type -> Type))
    (Proof ValidNarrativeTrait) (Proof TypeNarrativeCap)
    (Record ((a Int imm) (b Bool imm)))
    (Record ((b Bool imm) (a Int imm)))
    (Untrusted Int) (Refined Int (Prop p))
    (Union Int Bool) (Union Bool Int)
    (Intersection Int Bool)))

(test-case
 "tycode is injective over the type fixtures"
 (for ([type (in-list type-fixtures)])
   (check-true (redex-match? G2m τ type) (format "~s is a type" type))
   (check-true (redex-match? PR ptycode (tycode type))
               (format "~s has a PR type code" type)))
 (define codes (map tycode type-fixtures))
 (check-equal? (length codes) (set-count (list->set codes))))

(test-case
 "tycode separates types that type-equiv? identifies"
 ;; 正規化すると R-HandleSkip が別物として扱う 2 つの op を目標側が同一視する
 ;; （backend-matrix.md §5）。
 (check-not-equal? (tycode '(Union Int Bool)) (tycode '(Union Bool Int)))
 (check-not-equal? (tycode '(Record ((a Int imm) (b Bool imm))))
                   (tycode '(Record ((b Bool imm) (a Int imm))))))

(test-case
 "the target machine's Bool tags agree with tag-code"
 ;; backend-matrix.md §7、§10。食い違うと PMatch の枝が選べない。
 (check-eq? bool-tag-true (tag-code 'true))
 (check-eq? bool-tag-false (tag-code 'false))
 (check-equal? (lower-value-ok '(Construct Bool true))
               `(PTagged ,bool-tag-true)))

;;; backend-matrix.md §7 の値の表

(test-case
 "the value table of backend-matrix.md §7"
 (check-equal? (lower-value-ok 7) 7)
 (check-equal? (lower-value-ok 'unit) 'unit)
 (check-equal? (lower-value-ok "s") "s")
 (check-equal? (lower-value-ok '(Construct (Option Int) Some 1))
               `(PTagged ,(tag-code 'Some) 1))
 (check-equal? (lower-value-ok '(resource 3)) '(PResource 3))
 (check-equal? (lower-value-ok '(Lam User c0 (a) a))
               `(PClosure () (,(var-code 'a)) ,(var-code 'a)))
 (check-equal? (lower-value-ok '(PrimVal (Reserved o-add) add))
               `(PClosure () (pa_1 pa_2) (PPrim ,(shim 'add) pa_1 pa_2)))
 (check-equal? (lower-value-ok '(PrimVal (Reserved o-acquire) acquire))
               `(PClosure () (pa_1) (PPrim ,(shim 'acquire) pa_1)))
 (check-equal? (lower-value-ok '(CurryVal User (Lam User c0 (a b) a) 1))
               `(PClosure ((,(var-code 'a) 1)) (,(var-code 'b)) ,(var-code 'a)))
 (check-equal? (lower-value-ok '(RecurVal c0 f (a) a))
               `(PClosure () (,(var-code 'a))
                          (PLetrec ,(var-code 'f)
                                   (PLam (,(var-code 'a)) ,(var-code 'a))
                                   (PApp ,(var-code 'f) ,(var-code 'a)))))
 (check-equal? (lower-value-ok '(TypeRep User Int Type)) '(PTagged typerep))
 (check-equal? (lower-value-ok '(ProofRep User TypeNarrativeCap))
               '(PTagged proof))
 (check-equal? (lower-value-ok '(Rec ((a imm 1) (b imm 2))))
               `(PRec ((,(label-code 'a) 1) (,(label-code 'b) 2))))
 (check-equal? (lower-value-ok '(UVal 1)) '(PTagged uval 1))
 (check-equal? (lower-value-ok '(RVal (ProofRep User TypeNarrativeCap) 1))
               '(PTagged rval 1)))

(test-case
 "the fixed tags lowering invents never collide with encoded tags"
 ;; backend-matrix.md §7。源の K が typerep でも写し先は k:typerep になる。
 (check-not-equal? (tag-code 'typerep) 'typerep)
 (check-not-equal? (tag-code 'proof) 'proof)
 (check-not-equal? (tag-code 'uval) 'uval)
 (check-not-equal? (tag-code 'rval) 'rval)
 ;; prim-body の parameter も同じ理由で捕獲されない。
 (check-not-equal? (var-code 'pa_1) 'pa_1)
 (check-equal? (lower-value-ok '(Construct (Option Int) typerep 1))
               `(PTagged ,(tag-code 'typerep) 1)))

(test-case
 "primitive arity comes from Γ0, not from a copy"
 (check-equal? (primitive-arity 'add) 2)
 (check-equal? (primitive-arity 'acquire) 1)
 (check-false (primitive-arity 'not-a-primitive))
 (check-equal? (sort shim-primitives symbol<?)
               '(acquire add eq le lt mul sub))
 ;; 算術と比較の 6 件と資源取得を分けておく。
 ;; backend-matrix.md §10 の表の検査は前者だけを対象にする（G3c）。
 (check-equal? (sort arithmetic-primitives symbol<?) '(add eq le lt mul sub))
 (check-equal? resource-primitives '(acquire)))

;;; backend-matrix.md §7 の計算の表

(test-case
 "the computation table of backend-matrix.md §7"
 (check-equal? (lower-ok 'x) (var-code 'x))
 (check-equal? (lower-ok '(Apply (Lam User c0 (a) a) 1))
               `(PApp (PClosure () (,(var-code 'a)) ,(var-code 'a)) 1))
 (check-equal? (lower-ok '(Let (a Int) 1 a))
               `(PLet ,(var-code 'a) 1 ,(var-code 'a)))
 (check-equal? (lower-ok '(Let (a (Owned Res)) (resource 1) a))
               `(PLetOwned ,(var-code 'a) (PResource 1) ,(var-code 'a)))
 (check-equal? (lower-ok '(Let (a const Int) 1 a))
               `(PLet ,(var-code 'a) 1 ,(var-code 'a)))
 (check-equal? (lower-ok '(Let (a let (Owned Res)) (resource 1) a))
               `(PLetOwned ,(var-code 'a) (PResource 1) ,(var-code 'a)))
 (check-equal? (lower-ok '(Construct (Option Int) Some x))
               `(PTagged ,(tag-code 'Some) ,(var-code 'x)))
 (check-equal? (lower-ok '(Eliminate x ((Some (a) -> a))))
               `(PMatch ,(var-code 'x)
                        ((,(tag-code 'Some) (,(var-code 'a)) -> ,(var-code 'a)))))
 (check-equal? (lower-ok '(Perform (Return io Int) 1))
               `(PEffect (return ,(boundary-code 'io) ,(tycode 'Int)) 1))
 (check-equal? (lower-ok '(Handle (Return io Int) (a -> a) 1))
               `(PInstall (return ,(boundary-code 'io) ,(tycode 'Int))
                          (PLam (,(var-code 'a)) ,(var-code 'a))
                          1))
 (check-equal? (lower-ok '(Scope (0 1) x)) `(PScopeExit (0 1) ,(var-code 'x)))
 (check-equal? (lower-ok '(Recur c0 f (a) a x))
               `(PLetrec ,(var-code 'f)
                         (PLam (,(var-code 'a)) ,(var-code 'a))
                         ,(var-code 'x)))
 (check-equal? (lower-ok '(Yield 1 2)) '(PRuntime yield 1 2))
 (check-equal? (lower-ok '(Suspend 1)) '(PRuntime suspend 1))
 (check-equal? (lower-ok '(Move x)) `(PRuntime move ,(var-code 'x)))
 (check-equal? (lower-ok '(Move 0)) '(PRuntime move (PPlace 0)))
 (check-equal? (lower-ok '(Drop x)) `(PRuntime drop ,(var-code 'x)))
 (check-equal? (lower-ok '(Curry x 1)) `(PRuntime curry ,(var-code 'x) 1))
 (check-equal? (lower-ok '(Rec ((a imm x))))
               `(PRec ((,(label-code 'a) ,(var-code 'x)))))
 (check-equal? (lower-ok '(Proj x a)) `(PProj ,(var-code 'x) ,(label-code 'a)))
 (check-equal? (lower-ok '(Discharge (ProofRep User TypeNarrativeCap) x))
               (var-code 'x))
 (check-equal? (lower-ok '(Error 0)) '(PError 0)))

;;; backend-matrix.md §7 の feature 対応に使う形の突合と、形ごとの fixture

;; 左辺は lang.rkt の c と v の全形の頭シンボルである。G1m が足す (Error p) と
;; w ::= p に由来する (Move p) を含める。kind は lower と lower-value のどちらを
;; 呼ぶかを指す。
(define form-fixtures
  '((%literal  value 1)
    (%variable core  x)
    (Apply     core  (Apply (Lam User c0 (a) a) 1))
    (Let       core  (Let (a Int) 1 a))
    (Construct core  (Construct (Option Int) Some x))
    (Eliminate core  (Eliminate x ((Some (a) -> a))))
    (Perform   core  (Perform (Return io Int) 1))
    (Handle    core  (Handle (Return io Int) (a -> a) 1))
    (Scope     core  (Scope (0) x))
    (Recur     core  (Recur c0 f (a) a x))
    (Yield     core  (Yield 1 2))
    (Suspend   core  (Suspend 1))
    (Move      core  (Move x))
    (Drop      core  (Drop x))
    (Curry     core  (Curry x 1))
    (Rec       core  (Rec ((a imm x))))
    (Proj      core  (Proj x a))
    (Discharge core  (Discharge (ProofRep User TypeNarrativeCap) x))
    (Error     core  (Error 0))
    (resource  value (resource 3))
    (Lam       value (Lam User c0 (a) a))
    (PrimVal   value (PrimVal (Reserved o-add) add))
    (CurryVal  value (CurryVal User (Lam User c0 (a b) a) 1))
    (RecurVal  value (RecurVal c0 f (a) a))
    (TypeRep   value (TypeRep User Int Type))
    (ProofRep  value (ProofRep User TypeNarrativeCap))
    (UVal      value (UVal 1))
    (RVal      value (RVal (ProofRep User TypeNarrativeCap) 1))))

(test-case
 "the form table's left-hand side matches the fixture roster"
 ;; backend-matrix.md §7。lang.rkt の形の集合は公開 API で取れないので、
 ;; この 2 つの手書きの一覧を突き合わせる形で二重定義を許す。
 ;; lang.rkt に形が増えたとき、どちらか一方だけを更新すればこの検査が落ちる。
 (check-equal? (list->set (map first core-form-features))
               (list->set (map first form-fixtures))))

;; 目標項に τ が残っていないことを、型の構成子が像に無いことで確かめる
;; （backend-matrix.md §5）。符号化を通った名前はすべて : を含むので、
;; 素の構成子が残ればここで見つかる。
(define type-constructors
  '(Int Bool Unit String Never Res List Option Result Owned NFn TypeInfo Proof
    Record Untrusted Refined Union Intersection Type))

(define (type-free? value)
  (cond
    [(pair? value) (andmap type-free? value)]
    [(symbol? value) (not (memq value type-constructors))]
    [else #t]))

(test-case
 "lower is total over the form fixtures and its image is type-free"
 (for ([row (in-list form-fixtures)])
   (define head (first row))
   (define fixture (third row))
   (define-values (status result)
     (if (eq? (second row) 'value)
         (lower-value fixture 'racket-cs)
         (lower fixture 'racket-cs)))
   ;; memq は真のとき非空リストを返すので check-not-false を使う。
   (check-not-false (memq status '(ok capability))
                    (format "~a: ~a" head status))
   (when (eq? status 'ok)
     (check-true (redex-match? PR pc result) (format "~a: ~s" head result))
     (check-true (type-free? result) (format "~a: ~s" head result)))))

;;; backend-matrix.md §7 の衝突名 regression fixture

;; 変数名に return と prt の 5 名と PLet を使い、ADT tag に yield、record の
;; field 名に drop、Effect 境界の名前に PInstall を使う。符号化を外すと写し先が
;; PR の項にならないか、束縛と参照が食い違って stuck する。
(define collision-source
  '(Handle (Return PInstall Int) (PLam -> PLam)
     (Let (return Int) 1
       (Let (move Int) return
         (Let (PProj Int) move
           (Let (PTagged Int) PProj
             (Let (suspend Int) PTagged
               (Let (curry Int) suspend
                 (Eliminate (Construct (Option Int) yield curry)
                            ((yield (PLet) ->
                               (Yield (Proj (Rec ((drop imm PLet))) drop)
                                      (Perform (Return PInstall Int)
                                               PLet)))))))))))))

(test-case
 "a source term whose names are PR literals lowers and behaves identically"
 (define target (lower-ok collision-source))
 (check-true (redex-match? PR pc target))
 (define source-result (obs-eval-g2 collision-source depth fuel))
 (define target-result (obs-eval-pr target depth fuel))
 (check-equal? target-result source-result)
 ;; 空虚な一致を避ける。観測が 1 つ出て値で終わることを確かめる。
 (check-equal? (second source-result) 'value)
 (check-equal? (length (first source-result)) 1))

;;; backend-matrix.md §7 と backend-matrix.md §8：診断 ID ごとの fixture

(test-case
 "a kernel primitive produces the kernel-primitive diagnostic"
 (define name (first (first kernel-gamma0-entries)))
 (define diagnostic (lower-diagnostic `(PrimVal (Reserved o-kernel) ,name)))
 (check-equal? (diagnostic-id diagnostic) "E-LOW-001"))

(test-case
 "a trait primitive produces the trait-primitive diagnostic"
 (define name (first (first trait-gamma0-entries)))
 (define diagnostic (lower-diagnostic `(PrimVal (Reserved o-trait) ,name)))
 (check-equal? (diagnostic-id diagnostic) "E-LOW-002"))

(test-case
 "a form outside the table produces the unknown-core-form diagnostic"
 (define diagnostic (lower-diagnostic '(Frobnicate 1)))
 (check-equal? (diagnostic-id diagnostic) "E-LOW-003"))

(test-case
 "an op carrying a non-type produces the unknown-core-type diagnostic"
 ;; backend-matrix.md §8 の fail-closed 契約。近似的な符号を作って先へ進めない。
 (define diagnostic (lower-diagnostic '(Perform (Return io NotAType) 1)))
 (check-equal? (diagnostic-id diagnostic) "E-LOW-004"))

(test-case
 "a diagnostic comes back with no target term"
 ;; backend-matrix.md §8。部分的な出力と診断を同時に返さない。
 (define-values (status result) (lower '(Frobnicate 1) 'racket-cs))
 (check-eq? status 'capability)
 (check-true (diagnostic? result))
 (check-true (diagnostic-valid? result))
 ;; reason 文字列は found へ入る。移行前に検査していた「空でない文字列」を
 ;; found の側で固定し、同じ文字列が同じ経路から来ていることを確かめる。
 (define-values (seam-status seam-result)
   (lower/with-matrix '(Frobnicate 1) 'racket-cs backend-features))
 (check-eq? seam-status 'capability)
 (check-equal? (diagnostic-found result)
               (capability-diagnostic-reason seam-result))
 (check-true (string? (diagnostic-found result)))
 (check-false (string=? (diagnostic-found result) "")))

(test-case
 "lower-value も Diagnostic を返す"
 ;; 入口が 2 つあるため、片方だけ変換したまま残らないことを固定する。
 (define name (first (first kernel-gamma0-entries)))
 (define-values (status result)
   (lower-value `(PrimVal (Reserved o-kernel) ,name) 'racket-cs))
 (check-eq? status 'capability)
 (check-true (diagnostic? result))
 (check-equal? (diagnostic-id result) "E-LOW-001"))

(test-case
 "lowering の primary-span は棄却した節点である"
 ;; spec §17 完了条件 1。根ではなく内側の節点を指す。
 (define name (first (first kernel-gamma0-entries)))
 (define nested
   `(Drop (#:span src 0 40)
          (Drop (#:span src 5 35)
                (PrimVal (#:span src 10 30) (Reserved o-kernel) ,name))))
 (check-equal? (diagnostic-primary-span (lower-diagnostic nested))
               '(#:span src 10 30))
 ;; 同じ span を持つ節点が複数現れても、棄却した節点の span を返す。
 (define shared
   `(Drop (#:span src 0 20)
          (PrimVal (#:span src 0 20) (Reserved o-kernel) ,name)))
 (check-equal? (diagnostic-primary-span (lower-diagnostic shared))
               '(#:span src 0 20)))

(test-case
 "the diagnostic roster is exactly the set the fixtures produce"
 (check-equal? (list->set (map first diagnostic-ids))
               (set 'kernel-primitive 'trait-primitive
                    'unknown-core-form 'unknown-core-type)))

;;; backend-matrix.md §5 の test seam

;; 正典表の 1 行だけを unsupported へ差し替えた表を作る。列の形は変えない。
(define (matrix-with feature-id support)
  (for/list ([row (in-list backend-features)])
    (if (eq? (first row) feature-id)
        (list feature-id support support #f #f "test seam")
        row)))

(test-case
 "lower/with-matrix reads the injected table"
 (define source '(Apply (Lam User c0 (a) a) 1))
 (define-values (status result)
   (lower/with-matrix source 'racket-cs (matrix-with 'closure 'unsupported)))
 (check-eq? status 'capability)
 (check-eq? (capability-diagnostic-feature-id result) 'closure)
 (check-eq? (capability-diagnostic-backend result) 'racket-cs)
 ;; 正典表では同じ入力が通る。production の入口は表を取らない。
 (define-values (canonical-status canonical-result) (lower source 'racket-cs))
 (check-eq? canonical-status 'ok)
 (check-true (redex-match? PR pc canonical-result)))

;;; spec §18、§19。spanful な走査が spanless な走査と同じ判定を返すことを固定する。

;; primary-span を除いた署名。span は Task 3 で意図的に変わるため比べない。
(define (lower-signature term)
  (define-values (status result) (lower term 'racket-cs))
  (if (eq? status 'capability)
      (list status (diagnostic-id result) (diagnostic-found result))
      (list status result)))

(define parity-terms
  (list
   ;; 通る入力。
   `(Drop (#:span src 0 10) (#:lit 1 (#:span src 6 7)))
   `(Apply (#:span src 0 40)
           (Lam (#:span src 4 20) User c0
                ((#:bind a (#:span src 9 10)))
                (#:var a (#:span src 15 16)))
           (#:lit 2 (#:span src 30 31)))
   `(Let (#:span src 0 30)
         ((#:bind x (#:span src 4 5)) (#:ty Int (#:span src 7 10)))
         (#:lit 1 (#:span src 13 14))
         (#:var x (#:span src 20 21)))
   `(Perform (#:span src 0 30)
             (Return io (#:ty Int (#:span src 12 15)))
             (#:lit 1 (#:span src 25 26)))
   ;; m ::= imm mut（lang.rkt:164）であり many は m ではない。
   `(Rec (#:span src 0 20)
         (((#:lbl a (#:span src 4 5)) imm (#:lit 1 (#:span src 8 9)))))
   ;; w ::= vr（span-core.rkt）であり lt は w ではない。
   `(Move (#:span src 0 8) (#:var y (#:span src 6 7)))
   ;; 棄却される入力。
   `(Frobnicate (#:span src 0 12) 1)
   `(PrimVal (#:span src 0 18) (Reserved o-kernel) ,(first (first kernel-gamma0-entries)))
   `(Perform (#:span src 0 30)
             (Return io (#:ty NotAType (#:span src 12 20)))
             (#:lit 1 (#:span src 25 26)))))

(test-case "spanful な入力は spanless な入力と同じ判定を返す"
  (for ([term (in-list parity-terms)])
    (check-equal? (lower-signature term)
                  (lower-signature (erase-core term))
                  (format "parity: ~s" term))))

(test-case "parity fixture は空虚でない"
  ;; すべて棄却へ倒れていると parity が自明に成り立つため、通る入力の存在を要求する。
  (check-true
   (for/or ([term (in-list parity-terms)])
     (eq? 'ok (first (lower-signature term))))))
