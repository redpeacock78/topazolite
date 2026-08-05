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
