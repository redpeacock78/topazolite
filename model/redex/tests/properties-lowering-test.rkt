#lang racket

(require racket/list
         racket/match
         racket/set
         rackunit
         redex/reduction-semantics
         "../gen.rkt"
         "../lang.rkt"
         "../lowering.rkt"
         "../obs.rkt"
         "../origins.rkt"
         "../pr-lang.rkt"
         "../pr-machine.rkt"
         "../pr-obs.rkt"
         "../type-equiv.rkt"
         "../typing.rkt")

(define limits (read-bounds))
(define depth (bounds-observation-depth limits))
(define source-fuel (bounds-fuel limits))

;;; §7.1 repr 適合の単位検査

(test-case "§7.1: repr の表が τ の各行で成り立つ"
  (check-true (repr-ok? 'Int 7))
  (check-false (repr-ok? 'Int 'unit))
  (check-true (repr-ok? 'Bool (term (PTagged ,(tag-code 'true)))))
  (check-true (repr-ok? 'Bool (term (PTagged ,(tag-code 'false)))))
  (check-false (repr-ok? 'Bool (term (PTagged ,(tag-code 'Nil)))))
  (check-true (repr-ok? 'Unit 'unit))
  (check-true (repr-ok? 'String "a"))
  ;; Never に属する値は無い。どの値でも偽である。
  (check-false (repr-ok? 'Never 'unit))
  (check-true (repr-ok? 'Res (term (PResource 0))))
  (check-true (repr-ok? (term (List Int)) (term (PTagged ,(tag-code 'Nil)))))
  (check-true (repr-ok? (term (Option Int))
                        (term (PTagged ,(tag-code 'Some) 1))))
  (check-true (repr-ok? (term (Result Int Bool))
                        (term (PTagged ,(tag-code 'Ok) 1))))
  ;; 所有は静的な区別なので実行時表現に現れない。
  (check-true (repr-ok? (term (Owned Res)) (term (PResource 0))))
  (check-true (repr-ok? (term (NFn (Int) Int () ()))
                        (term (PClosure () (pa_1) pa_1))))
  (check-false (repr-ok? (term (NFn (Int) Int () ())) 7))
  (check-true (repr-ok? (term (TypeInfo Type)) (term (PTagged typerep))))
  (check-true (repr-ok? (term (Proof ValidNarrativeTrait))
                        (term (PTagged proof))))
  (check-true (repr-ok? (term (Record ((f Int)))) (term (PRec ()))))
  (check-true (repr-ok? (term (Untrusted Int)) (term (PTagged uval 1))))
  (check-false (repr-ok? (term (Untrusted Int)) (term (PTagged uval unit))))
  (check-true (repr-ok? (term (Refined Int ValidNarrativeTrait))
                        (term (PTagged rval 1))))
  ;; spec §7.1 の表に行が無い 2 形。表を分配して補った行である。
  (check-true (repr-ok? (term (Union Int Bool)) 7))
  (check-true (repr-ok? (term (Union Int Bool))
                        (term (PTagged ,(tag-code 'true)))))
  (check-false (repr-ok? (term (Union Int Unit)) "a"))
  (check-true (repr-ok? (term (Intersection Int (Union Int Bool))) 7))
  (check-false (repr-ok? (term (Intersection Int Bool)) 7)))

;;; §7.2 ラベル種別の単位検査

(test-case "§7.2: row-kinds が ℓ の 6 形を種別へ写す"
  (check-equal? (row-kinds (term ((Return b Int))))
                (set (term (return ,(boundary-code 'b) ,(tycode 'Int)))))
  ;; 同じ境界名でも τ が違えば別の種別になる。Handle の row-difference と
  ;; R-PR-InstallSkip がどちらも pop 全体を比べるのに合わせた粒度である。
  (check-false (equal? (row-kinds (term ((Return b Int))))
                       (row-kinds (term ((Return b Bool))))))
  (check-equal? (row-kinds (term ((Yield Int)))) (set 'yield))
  ;; (Yield τ) の型成分は落ちる。狭めとして spec §13 に記録済みである。
  (check-equal? (row-kinds (term ((Yield Int)))) (row-kinds (term ((Yield Bool)))))
  (check-equal? (row-kinds (term (Suspend Partial Compile Own)))
                (set 'suspend 'partial 'compile 'own))
  (check-equal? (row-kinds '()) (set)))

;;; §7.2 effect-kinds-of の形ごとの被覆

;; PR の形を 1 つずつ並べ、寄与を固定する。spec §7.2 の表の「その他」へ黙って
;; 落ちる形が出ないよう、§8.3 の形ごとの fixture と同じ流儀で表にする。Redex 9.2
;; は言語定義から形の一覧を取り出す API を持たないため、一覧は手で書く
;; （pr-lang-test.rkt と同じ制約である）。
(define sample-op (term (return ,(boundary-code 'b) ,(tycode 'Int))))
(define sample-op2 (term (return ,(boundary-code 'b) ,(tycode 'Bool))))
(define effectful (term (PEffect ,sample-op 1)))

(define target-form-fixtures
  (list
   ;; 値の形。現在行はすべて空である。
   (list 'integer 1 (set))
   (list 'unit 'unit (set))
   (list 'string "a" (set))
   (list 'variable (term v:x) (set))
   (list 'PResource (term (PResource 0)) (set))
   (list 'PPlace (term (PPlace 0)) (set))
   (list 'PClosure (term (PClosure () (pa_1) ,effectful)) (set))
   ;; PLam。spec §7.2 の表に行が無いので足した行である。
   (list 'PLam (term (PLam (pa_1) ,effectful)) (set))
   ;; 計算の形。
   (list 'PApp
         (term (PApp (PClosure () () ,effectful) 1))
         (set sample-op))
   (list 'PLet (term (PLet v:x ,effectful 1)) (set sample-op))
   (list 'PLetOwned (term (PLetOwned v:x ,effectful 1)) (set sample-op))
   ;; Recur の写し。PLam の寄与が空なので、残るのは継続の行だけである。
   (list 'PLetrec
         (term (PLetrec v:f (PLam () ,effectful) 1))
         (set))
   (list 'PTagged (term (PTagged k:Some ,effectful)) (set sample-op))
   (list 'PRec (term (PRec ((f:a ,effectful)))) (set sample-op))
   (list 'PProj (term (PProj (PRec ((f:a ,effectful))) f:a)) (set sample-op))
   (list 'PMatch
         (term (PMatch ,effectful ((k:Some (v:y) -> (PEffect ,sample-op2 1)))))
         (set sample-op sample-op2))
   (list 'PPrim (term (PPrim tz:add ,effectful 1)) (set sample-op))
   (list 'PEffect effectful (set sample-op))
   ;; handler の行は足し、本体からは pop 全体に等しい要素だけを引く。
   (list 'PInstall
         (term (PInstall ,sample-op (PLam (v:x) (PEffect ,sample-op2 1))
                         ,effectful))
         (set sample-op2))
   (list 'PRuntime-move (term (PRuntime move (PPlace 0))) (set 'own))
   (list 'PRuntime-drop (term (PRuntime drop ,effectful)) (set 'own sample-op))
   (list 'PRuntime-yield
         (term (PRuntime yield 1 ,effectful))
         (set 'yield sample-op))
   (list 'PRuntime-suspend
         (term (PRuntime suspend ,effectful))
         (set 'suspend sample-op))
   ;; Curry の row は function row と argument row の和で、何も足さない。
   (list 'PRuntime-curry
         (term (PRuntime curry (PClosure () (pa_1) pa_1) ,effectful))
         (set sample-op))
   ;; Scope の row は body の row そのもので、own を足さない。
   (list 'PScopeExit (term (PScopeExit (0) ,effectful)) (set sample-op))
   (list 'PError (term (PError 0)) (set))))

(test-case "§7.2: effect-kinds-of の寄与が形ごとに固定されている"
  (for ([fixture (in-list target-form-fixtures)])
    (match-define (list label target expected) fixture)
    (check-true (redex-match? PR pc target) (format "PR の項でない: ~a" label))
    (check-equal? (effect-kinds-of target) expected (format "~a" label))))

(test-case "§7.2: latent-kinds は関数値の本体だけを開く"
  (check-equal? (latent-kinds (term (PClosure () (pa_1) ,effectful)))
                (set sample-op))
  (check-equal? (latent-kinds (term (PLam (pa_1) ,effectful))) (set sample-op))
  ;; 構文上の関数値でない適用先からは何も取れない。過小近似である。
  (check-equal? (latent-kinds (term v:f)) (set))
  (check-equal? (latent-kinds 1) (set)))

(test-case "§7.2: latent-visible? は適用先が構文上の関数値かを見る"
  (check-true (latent-visible? (term (PApp (PClosure () () 1)))))
  (check-true (latent-visible? (term (PApp (PLam () 1)))))
  (check-false (latent-visible? (term (PApp v:f 1))))
  ;; 部分項の中の PApp も見る。
  (check-false (latent-visible? (term (PLet v:x 1 (PApp v:f 1)))))
  (check-true (latent-visible? (term (PLet v:x 1 (PApp (PLam () 1))))))
  ;; PApp を含まない項は真である。
  (check-true (latent-visible? (term (PEffect ,sample-op 1)))))

;;; §7.2 latent-tight?

;; typing.rkt:28 の lookup と :33 の owned-type? と :110 の extend と :112 の
;; without-owned は非公開である。lookup は origins.rkt が同じ実装を公開して
;; いるのでそちらを使い、残る 3 つだけを局所に置く。typing.rkt の公開面を
;; 広げるより軽い。
(define (owned-type? type)
  (match type [`(Owned ,_) #t] [_ #f]))

(define (extend environment names types)
  (append (map list names types) environment))

(define (without-owned environment)
  (filter (lambda (entry) (not (owned-type? (second entry)))) environment))

;; spec §7.2。源項に現れる各 Lam と RecurVal について、宣言 latent row が本体の
;; 推論行と等しいかを見る。row-subset? で受理される「宣言が広い関数」を除く。
;;
;; environment を走査で運ぶのは、入れ子の Lam の本体を検査するとき外側の束縛が
;; 要るためである。運ぶ形は infer-lam（typing.rkt:364）と infer-recur-value
;; （:384）と同じにする。
;;
;; core-check-row が #f を返したときは偽を返す。環境の再構成が届かない位置では
;; 過小近似になるが、(2) の条件を狭める側なので (1) も (2) も壊さない。空振りには
;; 生成検査の証人の数え上げと、下の 4 本目の回帰 fixture で気付ける。
(define (latent-tight? core environment places callables)
  (define (signature-of callable) (lookup callables callable))

  ;; 本体の環境。self が #f でないとき RecurVal の self binding を足す。
  (define (body-environment callable parameters self environment)
    (match (signature-of callable)
      [`(NFn (,parameter-types ...) ,_ ,_ ,_)
       (and (= (length parameters) (length parameter-types))
            (extend (if self
                        (extend (without-owned environment)
                                (list self)
                                (list (signature-of callable)))
                        (without-owned environment))
                    parameters
                    parameter-types))]
      [_ #f]))

  (define (declared-row-tight? callable parameters body self environment)
    (match (signature-of callable)
      [`(NFn ,_ ,return-type ,latent-row ,_)
       (define inner (body-environment callable parameters self environment))
       (define body-row
         (and inner
              (core-check-row body places callables return-type inner)))
       ;; 行の比較は集合としての比較にする。normalize-effect-row は順序と重複を
       ;; 保つのでここでは使わない。
       (and body-row (row-equiv? body-row latent-row) #t)]
      [_ #f]))

  (let walk ([node core] [environment environment])
    (match node
      [`(Lam ,_ ,callable (,parameters ...) ,body)
       (and (declared-row-tight? callable parameters body #f environment)
            (walk body
                  (or (body-environment callable parameters #f environment)
                      environment)))]
      [`(RecurVal ,callable ,function (,parameters ...) ,body)
       (and (declared-row-tight? callable parameters body function environment)
            (walk body
                  (or (body-environment callable parameters function environment)
                      environment)))]
      ;; Recur は宣言行の一致を要求しない。継続は変数 f へ適用するので、写しの
      ;; (PApp px ...) で latent-visible? がすでに偽になり (2) の条件が立たない。
      ;; ここで一致を求めても被覆は増えないので、本体の走査だけ行う。
      [`(Recur ,callable ,function (,parameters ...) ,body ,continuation)
       (define self-signature (signature-of callable))
       (and (walk body
                  (or (body-environment callable parameters function environment)
                      environment))
            (walk continuation
                  (if self-signature
                      (extend environment (list function) (list self-signature))
                      environment)))]
      [`(Let (,x ,type) ,bound ,body)
       (and (walk bound environment)
            (walk body (extend environment (list x) (list type))))]
      [`(Let (,x ,_ ,type) ,bound ,body)
       (and (walk bound environment)
            (walk body (extend environment (list x) (list type))))]
      ;; handler の束縛変数の型は op の τ である（typing.rkt:641）。
      [`(Handle (Return ,_ ,type) (,x -> ,handler) ,body)
       (and (walk handler (extend environment (list x) (list type)))
            (walk body environment))]
      ;; 起源を担ぐ値の形。O ::= (Derived O (Curry v)) が内側に値を持つので、
      ;; 一般の対の走査に任せると起源の中の Lam を外側の環境で検査してしまう。
      [`(CurryVal ,_ ,function ,argument)
       (and (walk function environment) (walk argument environment))]
      [`(PrimVal ,_ ,_) #t]
      [`(TypeRep ,_ ,_ ,_) #t]
      [`(ProofRep ,_ ,_) #t]
      ;; Eliminate の分岐本体は束縛を足さずに走査する。分岐変数の型を源から
      ;; 再構成できないためである。分岐本体に Lam があるときは core-check-row が
      ;; #f を返して過小近似へ落ちる。
      [(? pair?)
       (and (walk (car node) environment) (walk (cdr node) environment))]
      [_ #t])))

;;; 源側の fixture を Typed Core の水準で置く

;; 表層構文を通すと boundary 名が elaborate 側で自動生成され、同じ b に別の τ を
;; 載せた Handle と Perform の組（3 本目の回帰 fixture）が書けない。型と行は
;; core-type-of で取る。
(define (core-fixture core callables)
  (match (core-type-of core '() callables)
    [(list type row) (list type row)]
    [_ (error 'core-fixture "型付かない fixture: ~s" core)]))

;; §7.2 の 2 段の性質をひとつの fixture について確かめる。
(define (check-effect-preservation label core callables
                                   #:tight? expected-tight?)
  (match-define (list _type row) (core-fixture core callables))
  (define-values (status target) (lower core 'racket-cs))
  (check-eq? status 'ok (format "~a: ~s" label target))
  (define expected (row-kinds row))
  (define actual (effect-kinds-of target))
  ;; (1) 全域の包含。
  (check-true (subset? actual expected)
              (format "~a: ~s ⊄ ~s" label actual expected))
  (define tight? (latent-tight? core '() '() callables))
  (check-equal? tight? expected-tight? (format "~a: latent-tight?" label))
  ;; (2) 2 つの条件が揃うときだけ等号。
  (when (and (latent-visible? target) tight?)
    (check-equal? actual expected (format "~a: 等号" label)))
  (list expected actual tight?))

(define add-prim (term (PrimVal (Reserved o-add) add)))

(test-case "§7.2 回帰 1: Effect を持たない Curry は両側とも空である"
  (match-define (list expected actual _)
    (check-effect-preservation "curry" (term (Curry ,add-prim 1)) '()
                               #:tight? #t))
  (check-equal? expected (set))
  (check-equal? actual (set)))

(test-case "§7.2 回帰 2: Scope は own を立てない"
  (match-define (list expected actual _)
    (check-effect-preservation "scope" (term (Scope () 1)) '()
                               #:tight? #t))
  (check-equal? expected (set))
  (check-equal? actual (set)))

;; 同じ境界名 b で τ が違う Handle と Perform の入れ子。ptycode の違いで handler
;; が選ばれず、源側の ε にも目標側の残差にも (return b:b ty:Bool) が残る。境界名
;; だけで差し引く定義だと目標側が空になり、この fixture が (2) の反例になる。
(test-case "§7.2 回帰 3: 境界名が同じで τ が違う Handle は差し引かない"
  (define core
    (term (Handle (Return b Int)
                  (x -> x)
                  (Perform (Return b Bool) (Construct Bool true)))))
  (match-define (list expected actual _)
    (check-effect-preservation "handle" core '() #:tight? #t))
  (check-equal? expected (set (term (return ,(boundary-code 'b)
                                            ,(tycode 'Bool)))))
  (check-equal? actual expected))

;; 宣言 latent row が本体の行と等しい closure への Apply。(2) の等号が立つ。
(test-case "§7.2 回帰 4: 宣言と本体が一致する closure は等号になる"
  (define callables (term ((c1 (NFn () Int ((Return b Int)) ())))))
  (define core
    (term (Apply (Lam User c1 () (Perform (Return b Int) 7)))))
  (match-define (list expected actual tight?)
    (check-effect-preservation "tight-apply" core callables #:tight? #t))
  (check-true tight?)
  (check-equal? expected (set (term (return ,(boundary-code 'b)
                                            ,(tycode 'Int)))))
  (check-equal? actual expected))

;; 宣言 latent row が本体より広い closure への Apply（elaborate-test.rkt:282 の
;; g と同じ形）。latent-tight? が偽なので (2) を要求せず、(1) の包含だけが立つ。
;; この fixture が無いと、(2) の条件を落としたときに検査が黙って通ってしまう。
(test-case "§7.2 回帰 5: 宣言が本体より広い closure は等号を要求しない"
  (define callables (term ((c1 (NFn () Unit (Suspend Own) ())))))
  (define core (term (Apply (Lam User c1 () unit))))
  (match-define (list expected actual tight?)
    (check-effect-preservation "loose-apply" core callables #:tight? #f))
  (check-false tight?)
  (check-equal? expected (set 'suspend 'own))
  (check-equal? actual (set))
  (check-true (subset? actual expected)))

;; ε の出所を固定する fixture。elaborate.rkt:793 の TypeMake と :813 の LetType は
;; 行へ Compile を足すが、typing.rkt には Compile を立てる規則が 1 つも無い。
;; §7.2 の ε は typing.rkt の行なので左辺は空集合であり、目標側の (PTagged typerep)
;; の残差も空集合で等号が立つ。この fixture が無いと、検査が ε を elaboration の
;; 側から取るよう戻ったときに気付けない。
(test-case "§7.2 回帰 6: ε は elaboration の行ではなく Typed Core の行である"
  (define source (term (LetType Box (TypeMake List) (TypeMake (Spec Box Int)))))
  (match-define (list core _type elaborated-row callables)
    (elaboration-result source))
  ;; elaboration の側は Compile を担ぐ。
  (check-equal? (row-kinds elaborated-row) (set 'compile))
  ;; typing.rkt の側は担がない。
  (match-define (list _core-type core-row) (core-fixture core callables))
  (check-equal? (row-kinds core-row) (set))
  (match-define (list expected actual _)
    (check-effect-preservation "typerep" core callables #:tight? #t))
  (check-equal? expected (set))
  (check-equal? actual (set)))

;; Γ0 の 7 件の primitive はいずれも latent row が () で本体に Effect が無いので、
;; latent-tight? を満たし等号が立つ。
(test-case "§7.2: Γ0 の 7 件の primitive で等号が立つ"
  (for ([name (in-list shim-primitives)])
    (define arity (primitive-arity name))
    (define arguments (for/list ([_ (in-range arity)]) 1))
    (define core
      (term (Apply (PrimVal (Reserved ,(string->symbol (format "o-~a" name)))
                            ,name)
                   ,@arguments)))
    (match-define (list expected actual tight?)
      (check-effect-preservation (format "~a" name) core '() #:tight? #t))
    (check-true tight?)
    (check-equal? expected (set))
    (check-equal? actual (set))))

;;; §7.3 と §7.4

;; §7.4。fuel_t を fuel_s から倍にしていき、N 回目でも timeout ならその項を
;; discard する。N は §16 で 4 に固定した。
(define fuel-attempts 4)

(define (obs-eval-pr/adaptive target observation-depth start-fuel)
  (let loop ([current start-fuel] [remaining fuel-attempts])
    (define result (obs-eval-pr target observation-depth current))
    (cond
      [(not (eq? (second result) 'timeout)) result]
      [(<= remaining 1) #f]
      [else (loop (* 2 current) (sub1 remaining))])))

;; 終端の pcfg を返す。届かなければ #f。obs-eval-pr へ depth 0 を渡すと
;; pr-obs.rkt:44 の (= (length observed) depth) が最初の周回で成り立ち、1 歩も
;; 簡約せずに 'observed を返すので、§7.1 の終端判定には使えない。run-pr は
;; fuel 切れのとき pcfg ではなく 'timeout という記号を返す（pr-machine.rkt:344）
;; ので、pcfg の分解の前にここで畳む。
(define (run-pr/adaptive target start-fuel)
  (let loop ([current start-fuel] [remaining fuel-attempts])
    (define result (run-pr (inject-pr target) current))
    (cond
      [(not (eq? result 'timeout)) result]
      [(<= remaining 1) #f]
      [else (loop (* 2 current) (sub1 remaining))])))

;; 観測列の写し。lower-value は 2 値を返すので status を畳む。
(define (lowered-value value)
  (define-values (status result) (lower-value value 'racket-cs))
  (and (eq? status 'ok) result))

;; 源と目標の観測列と終端種別を比べる。返り値は 'match / 'mismatch / 'discard。
;; 源側が timeout のときは源の観測が足りないので比べない。
(define (compare-observations core target observation-depth)
  (define source (obs-eval-g2 core observation-depth source-fuel))
  (cond
    [(eq? (second source) 'timeout) 'discard]
    [else
     (define result (obs-eval-pr/adaptive target observation-depth source-fuel))
     (cond
       [(not result) 'discard]
       [(and (equal? (map lowered-value (first source)) (first result))
             (eq? (second source) (second result)))
        'match]
       [else 'mismatch])]))

;;; §7.5 の 4 つの終端種別の fixture

;; 生成器の分布は偏るので、4 つの終端種別それぞれに決定的な fixture を置く。
(define (check-terminal-kind label core observation-depth expected-kind)
  (define-values (status target) (lower core 'racket-cs))
  (check-eq? status 'ok (format "~a: ~s" label target))
  (define source (obs-eval-g2 core observation-depth source-fuel))
  (check-eq? (second source) expected-kind (format "~a: 源の終端種別" label))
  (define result (obs-eval-pr/adaptive target observation-depth source-fuel))
  (check-true (and result #t) (format "~a: 目標が timeout のまま" label))
  (check-equal? (map lowered-value (first source)) (first result)
                (format "~a: 観測列" label))
  (check-eq? (second source) (second result)
             (format "~a: 終端種別の対応" label)))

(test-case "§7.5: 終端種別 value"
  (check-terminal-kind "value" (term (Apply ,add-prim 1 2)) depth 'value))

(test-case "§7.5: 終端種別 perform"
  (check-terminal-kind "perform" (term (Perform (Return b Int) 7)) depth
                       'perform))

;; 源項は (Error p) を直接含まない。(Error p) は型付かないためである。同じ場所を
;; 2 度 Move して R-MoveError に到達する形にする。machine-own-test.rkt:24 が
;; 同じ項で源側の (Error 0) を固定している。
(test-case "§7.5: 終端種別 ownership-error"
  (define acquire-prim (term (PrimVal (Reserved o-acquire) acquire)))
  (check-terminal-kind
   "ownership-error"
   (term (Let (r (Owned Res))
              (Apply ,acquire-prim 0)
              (Let (used Res) (Move r) (Move r))))
   depth
   'ownership-error))

;; 観測が d 個で打ち切られる項。d を 1 にして Yield を 2 段にする。
(test-case "§7.5: 終端種別 observed"
  (check-terminal-kind "observed" (term (Yield 1 (Yield 2 3))) 1 'observed))

;;; 生成検査

(define (bump! counter) (set-box! counter (add1 (unbox counter))))

;; 生成項は表層構文である。elaboration-result が (core type row callables) を
;; 返す（properties-test.rkt:29 と同じ流儀）。
(define (artifact source)
  (match (elaboration-result source)
    [(list core type row callables) (values core type row callables)]
    [other (error 'properties-lowering-test
                  "prepared term no longer elaborates: ~e" other)]))

(define repr-witness (box 0))
(define effect-nonempty-witness (box 0))
(define effect-tight-witness (box 0))
(define trace-compared (box 0))
(define trace-discarded (box 0))

;; §7.1。評価結果が値なら repr(τ) に属する。終端の core は run-pr/adaptive の
;; 返す pcfg から取り、種別は terminal-kind-pr で見る。obs-eval-pr を使わないのは
;; 上の run-pr/adaptive のコメントの理由による。
(define (repr-conforms? source)
  (define-values (core type _row callables) (artifact source))
  (define-values (status target) (lower core 'racket-cs))
  (cond
    [(not (eq? status 'ok)) #t]
    [else
     (define result (run-pr/adaptive target source-fuel))
     (cond
       [(not result) #t]
       [else
        (match-define `(pcfg ,value ,_ ,_ ,_) result)
        (cond
          [(not (eq? (terminal-kind-pr value) 'value)) #t]
          [else
           (bump! repr-witness)
           (repr-ok? type value)])])]))

;; §7.2 の 2 段。
;; ε は Typed Core の型付け判定の行である。elaboration-result の第 3 要素では
;; ない。elaborate.rkt:793 の TypeMake と :813 の LetType は行へ Compile を足す
;; が、typing.rkt には Compile を立てる規則が 1 つも無い。effect-kinds-of の表の
;; 各行の根拠を typing.rkt の規則に置いているので、比べる相手も typing.rkt の行で
;; なければならない。check-effect-preservation の core-fixture と同じ出所である。
(define (effect-kinds-sound? source)
  (define-values (core _type _elaborated-row callables) (artifact source))
  (match-define (list _core-type row) (core-fixture core callables))
  (define-values (status target) (lower core 'racket-cs))
  (cond
    [(not (eq? status 'ok)) #t]
    [else
     (define expected (row-kinds row))
     (define actual (effect-kinds-of target))
     (when (positive? (set-count expected)) (bump! effect-nonempty-witness))
     (and (subset? actual expected)
          (cond
            [(and (latent-visible? target)
                  (latent-tight? core '() '() callables))
             (bump! effect-tight-witness)
             (equal? actual expected)]
            [else #t]))]))

;; §7.3。
(define (trace-preserved? source)
  (define-values (core _type _row _callables) (artifact source))
  (define-values (status target) (lower core 'racket-cs))
  (cond
    [(not (eq? status 'ok)) #t]
    [else
     (match (compare-observations core target depth)
       ['discard (bump! trace-discarded) #t]
       ['match (bump! trace-compared) #t]
       ['mismatch (bump! trace-compared) #f])]))

(module+ test
  ;; properties-record-test.rkt:34 の bounded-check-g2 と同じ形である。証人の箱を
  ;; 引数に取るのは、性質ごとに「実際に主張が働いた項」の定義が違うためである。
  (define-syntax-rule (bounded-check-lowering test-name property witnesses)
    (test-case test-name
      (define counts (make-search-counts limits))
      (define result
        (call-with-search-seed
         limits
         (lambda ()
           (redex-check
            G2gen g #:ad-hoc
            (begin
              (note-accepted! counts)
              (property (term g)))
            #:attempts (bounds-attempts limits)
            #:attempt-size (lambda (_attempt) (bounds-term-depth limits))
            #:prepare (lambda (source) (prepare-elaborable counts source))
            #:print? #f))))
      (check-equal? result #t)
      (check-true (positive? (search-counts-accepted counts)))
      (for ([witness (in-list witnesses)])
        (check-true (positive? (unbox (cdr witness)))
                    (format "証人が 0 件である: ~a" (car witness))))
      (printf "~a: attempts=~a accepted=~a discard=~a~a seed=~a\n"
              test-name
              (bounds-attempts limits)
              (search-counts-accepted counts)
              (search-counts-discarded counts)
              (apply string-append
                     (for/list ([witness (in-list witnesses)])
                       (format " ~a=~a" (car witness) (unbox (cdr witness)))))
              (bounds-seed limits))))

  (bounded-check-lowering
   "BAK-001 §7.1: 値の表現が repr に適合する"
   repr-conforms?
   (list (cons 'value-terminal repr-witness)))

  (bounded-check-lowering
   "BAK-001 §7.2: Effect 種別が包含し、条件が揃えば等号になる"
   effect-kinds-sound?
   (list (cons 'nonempty-row effect-nonempty-witness)
         (cons 'tight effect-tight-witness)))

  (bounded-check-lowering
   "BAK-001 §7.3: 観測列と終端種別が一致する"
   trace-preserved?
   (list (cons 'compared trace-compared)))

  ;; §16。discard は受理項の半分を超えない。超えたときは fuel の与え方か生成器の
  ;; 分布のどちらかが壊れており、性質が実質的に空振りしている。
  (test-case "§7.4: discard 率が比較した項の半分を超えない"
    (printf "trace: compared=~a discarded=~a\n"
            (unbox trace-compared) (unbox trace-discarded))
    (check-true (<= (* 2 (unbox trace-discarded)) (unbox trace-compared))
                (format "discard=~a compared=~a"
                        (unbox trace-discarded) (unbox trace-compared)))))
