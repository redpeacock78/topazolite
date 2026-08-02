#lang racket

(require racket/match
         redex/reduction-semantics
         "origins.rkt"
         "policy.rkt"
         "traits.rkt"
         "type-equiv.rkt"
         "validators.rkt")

(provide make-goal goal? goal-proposition
         resolved Absent ambiguous
         search-result? resolved? absent? ambiguous?
         resolved-proof ambiguous-proofs
         candidateize initial-candidate-context Γ-pc0
         entry-phi entry-origin entry-cid entry-sid entry-pid entry-hook
         project project-goal scope-visible?
         candidate-proof candidate-prop candidate-origin
         candidate-cid candidate-sid candidate-pid candidate-hook
         candidate-identity hook-ok? hook-ok?/parts coherent-candidate?
         wf-candidate? wf-context? wf-Σ?
         resolve-candidates
         check-project-goal-return check-resolve-return check-discharge-return
         make-classifier make-oracle make-cert cert-valid? unique?
         default-classifier default-oracle
         admissible?
         discharge? current-search-log search-log-snapshot reset-search-log!
         obligations-dischargeable?)

;; Goal descriptor: (Goal φ ⊥ext)。⊥ext は型・Effect・lexical 特殊化の拡張点で G2b は空。
(define (make-goal phi) (list 'Goal phi '⊥ext))
(define (goal? x)
  (match x [(list 'Goal _ '⊥ext) #t] [_ #f]))
(define (goal-proposition g) (second g))

;; SearchResult: (Resolved P) | Absent | (Ambiguous (P ...))
(define (resolved P) (list 'Resolved P))
(define Absent 'Absent)
(define (ambiguous ps) (list 'Ambiguous ps))

(define (resolved? sr)  (match sr [(list 'Resolved _) #t] [_ #f]))
(define (absent? sr)    (eq? sr 'Absent))
(define (ambiguous? sr) (match sr [(list 'Ambiguous _) #t] [_ #f]))
(define (search-result? sr) (or (resolved? sr) (absent? sr) (ambiguous? sr)))

(define (resolved-proof sr) (second sr))
(define (ambiguous-proofs sr) (second sr))

;; candidateize: 固定の Π0 を初期候補文脈 Γ_pc⁰ へ変換する。
;; Π0 の各束縛 (name (φ O)) から entry (φ O cid sid pid hook) を作る。
;; cid は name 由来の安定な候補識別子、sid は root scope、pid は既定値。
;; いずれも Π0 から決定的に定め、gensym や counter で採番しない。
(define (candidateize pi0)
  (for/list ([binding (in-list pi0)])
    (match-define (list name (list phi origin)) binding)
    (list name (list phi origin name 'root 'default '()))))

;; 探索と elaboration が共有する初期候補文脈。propositions を省略した場合は
;; typing が使う固定の Π0 から作る。
(define (initial-candidate-context [propositions Π0])
  (append (candidateize propositions) (trait-global-bindings)))

(define Γ-pc0 (initial-candidate-context))

;; entry = (φ O cid sid pid hook)
(define (entry-phi e)    (first e))
(define (entry-origin e) (second e))
(define (entry-cid e)    (third e))
(define (entry-sid e)    (fourth e))
(define (entry-pid e)    (fifth e))
(define (entry-hook e)   (sixth e))

;; project: scope 文脈 sc-ctx から可視な entry だけを候補へ写す。
(define (project gamma-pc sc-ctx)
  (for/list ([binding (in-list gamma-pc)]
             #:when (scope-visible? (entry-sid (second binding)) sc-ctx))
    (define e (second binding))
    (list 'Candidate
          (list 'ProofRep (entry-origin e) (entry-phi e))
          (entry-cid e) (entry-sid e) (entry-pid e) (entry-hook e))))

;; TRT-004: 合成 trait への所属。goal の τ について、その trait を出力する
;; intersect 行ごとに成分候補の直積を作る。Γ_pc へは入れない。Γ_pc は正典表
;; から機械的に導く固定の表であり、goal の τ に依存する候補を置く場所ではない。
;; 停止性は intersect-table の非巡回性（intersect-acyclic?）から従う。
(define (compose-candidates gamma-pc sc-ctx goal)
  (match (goal-proposition goal)
    [`(Implements ,type ,tn-out)
     (define trait-row (trait-row-by-name tn-out))
     (cond
       [(not trait-row) '()]
       [else
        (define tid (trait-origin trait-row))
        (append*
         (for/list ([row (in-list intersect-table)]
                    #:when (eq? (intersect-output row) tn-out))
           (define iid (intersect-oid row))
           (define left
             (project-goal/impl
              gamma-pc sc-ctx
              (make-goal `(Implements ,type ,(intersect-left row)))))
           (define right
             (project-goal/impl
              gamma-pc sc-ctx
              (make-goal `(Implements ,type ,(intersect-right row)))))
           (for*/list ([a (in-list left)] [b (in-list right)])
             (define origin
               `(Derived (Reserved ,iid)
                         (Compose ,tn-out
                                  ,(candidate-origin a)
                                  ,(candidate-origin b))))
             (define hook
               (list 'compose tid iid
                     (list (candidate-origin a) (candidate-hook a))
                     (list (candidate-origin b) (candidate-hook b))))
             (list 'Candidate
                   (list 'ProofRep origin `(Implements ,type ,tn-out))
                   `(compose ,iid ,(candidate-cid a) ,(candidate-cid b))
                   'root
                   'default
                   hook))))])]
    [_ '()]))

;; project-goal: goal の命題に一致する entry だけを Σ へ写す。Γ_pc に別命題の
;; 候補が同居すると、それらが wf-Σ? を落として無関係な goal の discharge を
;; 妨げる。抽出の段階で goal 単位に絞る。
(define (project-goal/impl gamma-pc sc-ctx goal)
  (filter (lambda (c)
            (and (candidate-matches? c goal)
                 (coherent-candidate? c sc-ctx)))
          (append (project gamma-pc sc-ctx)
                  (compose-candidates gamma-pc sc-ctx goal))))

;; POL-002/TRT-003: 返る候補はすべて wf であり、系譜から可視な行だけを含む。
;; 空リストは候補が無い場合の fail-closed 返却であり、そのまま真とする。
(define (check-project-goal-return args returns)
  (match* (args returns)
    [((list _gamma-pc sc-ctx goal) (list sigma))
     (and (list? sigma)
          (or (null? sigma)
              (and (wf-Σ? sigma goal sc-ctx)
                   (for/and ([c (in-list sigma)])
                     (coherent-candidate? c sc-ctx)))))]
    [(_ _) #f]))

(define project-goal
  (policy-wrap 'TraitResolution 'project-goal
               project-goal/impl
               check-project-goal-return))

;; COH-001: scope の可視性は祖先到達で決まる。sc-ctx のいずれかの要素に
;; ついて、sid がその要素自身か祖先であるとき可視である。方向を逆に取ると
;; (root) から子 scope の宣言が見えてしまうため、この向きに固定する。
(define (scope-visible? sid sc-ctx)
  (for/or ([s (in-list sc-ctx)])
    (and (member sid (scope-ancestors s)) #t)))

;; cand = (Candidate (ProofRep O φ) cid sid pid hook)
(define (candidate-proof c)  (second c))
(define (candidate-prop c)   (third (candidate-proof c)))
(define (candidate-origin c) (second (candidate-proof c)))
(define (candidate-cid c)    (third c))
(define (candidate-sid c)    (fourth c))
(define (candidate-pid c)    (fifth c))
(define (candidate-hook c)   (sixth c))

;; 命題の同値。正準鍵が作れない場合は type-equiv? と同じ構文比較へ落ちる。
(define (candidate-matches? c goal)
  (proposition-equiv? (candidate-prop c) (goal-proposition goal)))

;; hook は Implements 候補を trait 行・impl 行・発行者へ束縛する。合成候補は
;; intersect 行と成分の (origin hook) を保持する。それ以外の候補は G2b までと
;; 同じ空 hook だけを持つ。
(define (hook-ok?/parts proposition origin hook)
  (match proposition
    [`(Implements ,type ,trait)
     (match hook
       [(list tid oid)
        (define trait-row (trait-row-by-name trait))
        (define impl-row (impl-row-by-oid oid))
        (and trait-row
             impl-row
             (equal? origin `(Reserved ,oid))
             (eq? tid (trait-origin trait-row))
             (eq? trait (impl-trait-name impl-row))
             (proposition-equiv?
              proposition
              `(Implements ,(impl-target-type impl-row)
                           ,(impl-trait-name impl-row))))]
       ;; TRT-004: 合成候補。hook は成分の origin と hook を再帰的に持ち、
       ;; origin 内の Compose と一致しなければならない。origin だけを見ると
       ;; 成分の hook が偽装でき、coherence 判定の錨が外れる。
       [(list 'compose tid iid (list origin-a hook-a) (list origin-b hook-b))
        (define row (intersect-row-by-oid iid))
        (define trait-row (trait-row-by-name trait))
        (and row
             trait-row
             (eq? (intersect-output row) trait)
             (eq? tid (trait-origin trait-row))
             (match origin
               [`(Derived (Reserved ,iid2) (Compose ,tn-out ,o-a ,o-b))
                (and (eq? iid2 iid)
                     (eq? tn-out trait)
                     (equal? o-a origin-a)
                     (equal? o-b origin-b))]
               [_ #f])
             (hook-ok?/parts `(Implements ,type ,(intersect-left row))
                             origin-a hook-a)
             (hook-ok?/parts `(Implements ,type ,(intersect-right row))
                             origin-b hook-b))]
       [_ #f])]
    ;; TRT-005: 暗黙充足された RequiresBoth は、その intersect 行の oid を持つ。
    [`(RequiresBoth ,left ,right)
     (match hook
       [(list iid)
        (define row (intersect-row-by-oid iid))
        (and row
             (eq? (intersect-left row) left)
             (eq? (intersect-right row) right)
             (equal? origin `(Reserved ,iid)))]
       [_ (null? hook)])]
    [_ (null? hook)]))

(define (hook-ok? c)
  (hook-ok?/parts (candidate-prop c)
                  (candidate-origin c)
                  (candidate-hook c)))

;; Implements 候補は trait または target type の生成 scope が現在の系譜から
;; 可視な場合だけ採る。entry 自体の root 可視性とは別の条件である。
;; 合成候補は成分を再帰的に見るため、候補ではなく命題・origin・hook を取る。
(define (coherent-parts? proposition origin hook sc-ctx)
  (match proposition
    [`(Implements ,type ,_)
     (and (hook-ok?/parts proposition origin hook)
          (match hook
            [(list tid oid)
             (define trait-row (trait-row-by-oid tid))
             (define impl-row (impl-row-by-oid oid))
             (and trait-row
                  impl-row
                  (or (scope-visible? (trait-scope trait-row) sc-ctx)
                      (scope-visible? (impl-target-scope impl-row) sc-ctx)))]
            ;; 合成候補には impl 行が無い。出力 trait の生成 scope が可視で
            ;; あり、かつ成分が二つとも coherent であることを錨にする。
            [(list 'compose tid iid (list origin-a hook-a) (list origin-b hook-b))
             (define trait-row (trait-row-by-oid tid))
             (define row (intersect-row-by-oid iid))
             (and trait-row
                  row
                  (scope-visible? (trait-scope trait-row) sc-ctx)
                  (coherent-parts? `(Implements ,type ,(intersect-left row))
                                   origin-a hook-a sc-ctx)
                  (coherent-parts? `(Implements ,type ,(intersect-right row))
                                   origin-b hook-b sc-ctx))]
            [_ #f]))]
    [`(RequiresBoth ,_ ,_)
     (hook-ok?/parts proposition origin hook)]
    [_ #t]))

(define (coherent-candidate? c sc-ctx)
  (coherent-parts? (candidate-prop c)
                   (candidate-origin c)
                   (candidate-hook c)
                   sc-ctx))

;; 候補同一性: requirement shape・provenance・cid・sid・pid・trait hook。
(define (candidate-identity c)
  (list (or (canonical-proposition-key (candidate-prop c))
            (candidate-prop c))
        (candidate-origin c)
        (candidate-cid c)
        (candidate-sid c)
        (candidate-pid c)
        (candidate-hook c)))

;; wf-candidate: 一つの候補が整合であること。
(define (wf-candidate? c goal [sc-ctx '(root)])
  (and (candidate-matches? c goal)
       (origin-ok? (candidate-origin c) (candidate-prop c))
       (scope-visible? (candidate-sid c) sc-ctx)
       (hook-ok? c)))

;; RFN-003: 候補の witness には発行者対応だけを課す。出現許可は成果物の判定
;; であり、探索文脈の候補には適用しない。Redex の metafunction を経由しない
;; ため、候補ごとの往復も減る。
(define (origin-ok? O phi)
  (proof-issuer-ok? R0 O phi))

;; wf-context?: Γ_pc の各 entry が単独で整合であること。goal に依らない判定で
;; あり、goal との一致は wf-Σ? が抽出後に見る。
(define (wf-context? gamma-pc)
  (for/and ([binding (in-list gamma-pc)])
    (define e (second binding))
    (and (origin-ok? (entry-origin e) (entry-phi e))
         (hook-ok?/parts (entry-phi e)
                         (entry-origin e)
                         (entry-hook e)))))

;; wf-Σ: すべての候補が wf-candidate を満たす。goal についての Finite 完全性は
;; project-goal が構成上保証する。
(define (wf-Σ? sigma goal [sc-ctx '(root)])
  (andmap (lambda (c) (wf-candidate? c goal sc-ctx)) sigma))

;; resolve-candidates: Finite closed-world の候補解決。全域で、wf-Σ を前提とする。
(define (resolve-candidates/impl goal sigma)
  ;; goal の命題に shape が一致する候補を集める
  (define matched
    (filter (lambda (c) (candidate-matches? c goal)) sigma))
  ;; raw 表現を先に整列し、同一性が同じ候補の代表を入力順に依存させない。
  (define raw-sorted
    (sort matched string<? #:key (lambda (c) (format "~s" c))))
  (define deduped
    (remove-duplicates raw-sorted #:key candidate-identity))
  ;; 同一性全体の canonical order で並べる。
  (define sorted
    (sort deduped string<?
          #:key (lambda (c) (format "~s" (candidate-identity c)))))
  (cond [(null? sorted) Absent]
        [(null? (cdr sorted)) (resolved (candidate-proof (car sorted)))]
        [else (ambiguous (map candidate-proof sorted))]))

;; POL-002/TRT-003: Resolved は候補 1 件、Ambiguous は 2 件以上。返した Proof は
;; いずれも Σ の候補が実際に抱えていたものである。件数の導出そのものを検査で
;; 組み直すと resolve-candidates の再実装になるため、返却と Σ の対応だけを見る。
(define (check-resolve-return args returns)
  (define (from-sigma? sigma P)
    (for/or ([c (in-list sigma)]) (equal? (candidate-proof c) P)))
  (match* (args returns)
    [((list _goal _sigma) (list 'Absent)) #t]
    [((list _goal sigma) (list (list 'Resolved P)))
     (from-sigma? sigma P)]
    [((list _goal sigma) (list (list 'Ambiguous ps)))
     (and (>= (length ps) 2)
          (= (length ps) (length (remove-duplicates ps)))
          (for/and ([P (in-list ps)]) (from-sigma? sigma P)))]
    [(_ _) #f]))

(define resolve-candidates
  (policy-wrap 'TraitResolution 'resolve-candidates
               resolve-candidates/impl
               check-resolve-return))

;; χ: goal と候補文脈から計算クラスへの trusted な写像。SR を参照しない。
;; goal を key に引くほか、key の有限列挙ができない命題のために shape 規則を
;; 持つ。どちらも SR を見ないため、trusted 性は変わらない。
(define (make-classifier table [shape-rule (lambda (goal gamma-pc) #f)])
  (lambda (goal gamma-pc)
    (cond [(assoc goal table) => cdr]
          [(shape-rule goal gamma-pc) => values]
          [else 'Unknown])))

;; 既定 χ: G1 の 2 命題と判定表の各命題を Finite に写す。常在性の命題は label
;; ごとに無限個あって表に列挙できないため、shape 規則で Finite に写す。
(define default-classifier
  (make-classifier
   (append
    (list (cons (make-goal 'TypeNarrativeCap) 'Finite)
          (cons (make-goal 'ValidNarrativeTrait) 'Finite))
    (for/list ([row (in-list validator-table)])
      (cons (make-goal (validator-proposition row)) 'Finite)))
   (lambda (goal gamma-pc)
     (match (goal-proposition goal)
       [`(Presence ,_) 'Finite]
       [`(FieldType ,_ ,_) 'Finite]
       [`(Implements ,_ ,_) 'Finite]
       [`(ValidNarrativeTrait ,_) 'Finite]
       [`(RequiresBoth ,_ ,_) 'Finite]
       [_ #f]))))

;; Ω: Productive 探索の結果と certificate を返す trusted な写像。無ければ #f。
(define (make-oracle table)
  (lambda (goal gamma-pc)
    (cond [(assoc goal table) => cdr]
          [else #f])))

;; 既定 Ω: Productive 候補を持たない。
(define default-oracle (make-oracle '()))

;; 一意性 certificate: goal・Γ_pc・候補 P・計算クラスに束縛された証拠。
(define (make-cert goal gamma-pc P) (list 'Cert goal gamma-pc P 'Productive))
(define (cert-valid? cert goal gamma-pc P)
  (equal? cert (list 'Cert goal gamma-pc P 'Productive)))

;; Finite の一意性: 完全な Σ に対して resolve が (Resolved P) を返すことが導出。
(define (unique? goal sigma P)
  (equal? (resolve-candidates/impl goal sigma) (resolved P)))

;; admissible?: 暗黙充足の可否。SR が (Resolved P) の枝だけで真になりうる。
;; ev は現在の探索に束縛された証拠（Finite: 完全な Σ、Productive: certificate）。
(define (admissible? goal gamma-pc class sr ev [sc-ctx '(root)])
  (match* (class sr)
    [('Finite (list 'Resolved P))
     ;; 完全な Σ からの一意性導出があり、その P が SR の P と一致（PSR-002）。
     ;; ev は goal 単位に抽出した Σ である。project の全体と比べると、別命題の
     ;; 候補が同居する Γ_pc で恒偽になる。
     (and ev
          (equal? ev (project-goal/impl gamma-pc sc-ctx goal))
          (wf-Σ? ev goal sc-ctx)
          (unique? goal ev P))]
    [('Productive (list 'Resolved P))
     ;; Ω の certificate が同じ goal・Γ_pc・P に束縛（PSR-002）
     (and ev (cert-valid? ev goal gamma-pc P))]
    [('Unknown _) #f]
    [(_ 'Absent) #f]
    [(_ (list 'Ambiguous _)) #f]
    [(_ _) #f]))

;; 探索起動の記録: 空虚な合格の防止。どの class・SR 枝と採否を通したかを覚える。
(define current-search-log (make-parameter (make-hash)))
(define (reset-search-log!) (current-search-log (make-hash)))
(define (search-log-snapshot) (hash-copy (current-search-log)))
(define (log-branch! key) (hash-set! (current-search-log) key #t))

(define (log-outcome! class sr accepted?)
  (define tag
    (if (eq? class 'Unknown)
        'unknown-reject
        (string->symbol
         (format "~a-~a-~a"
                 (string-downcase (symbol->string class))
                 (cond [(resolved? sr) 'resolved]
                       [(absent? sr) 'absent]
                       [else 'ambiguous])
                 (if accepted? 'accept 'reject)))))
  (log-branch! tag))

;; discharge?: 義務充足の judgment。χ で class を得て、class に応じて SR と
;; 証拠を得る。文脈そのものの整合（wf-context?）は class と SR に依らないため、
;; 抽出の前に一度だけ見る。
;; 分類と探索結果は返却値から読めない。検査述語の中で χ を計算し直すと
;; ProofSearch policy が自分自身を呼ぶことになるため、実装の側を厚くする。
;; log-outcome! の記録を読む形にしないのは、検証が計測用の仕組みへ依存し、
;; ログを初期化し忘れた場合に検査が黙って通るためである。
(define (discharge?/impl gamma-pc chi omega goal [sc-ctx '(root)])
  (define class (chi goal gamma-pc))
  (define-values (sr ev)
    (case class
      [(Finite)
       (define sigma (project-goal/impl gamma-pc sc-ctx goal))
       (values (resolve-candidates/impl goal sigma) sigma)]
      [(Productive)
       (match (omega goal gamma-pc)
         [(list sr cert) (values sr cert)]
         [_ (values Absent #f)])]
      [else (values Absent #f)]))
  (define accepted?
    (and (wf-context? gamma-pc)
         (admissible? goal gamma-pc class sr ev sc-ctx)))
  (log-outcome! class sr accepted?)
  (values accepted? class sr))

;; POL-002/PSR-002: 受理したなら分類は Finite か Productive であり、探索結果は
;; Resolved である。#f は fail-closed 返却であり素通りする。
(define (check-discharge-return args returns)
  (match returns
    [(list accepted? class sr)
     (and (boolean? accepted?)
          (search-result? sr)
          (or (not accepted?)
              (and (memq class '(Finite Productive)) (resolved? sr) #t)))]
    [_ #f]))

(define discharge?
  (policy-wrap 'ProofSearch 'discharge?
               discharge?/impl
               check-discharge-return
               #:project (lambda (vs) (list (first vs)))))

;; 義務列の全 φ が候補文脈から暗黙充足できるか。typing と elaborate の共有経路。
(define (obligations-dischargeable? obligations gamma-pc
                                    [chi default-classifier]
                                    [omega default-oracle])
  (for/and ([phi (in-list obligations)])
    (discharge? gamma-pc chi omega (make-goal phi))))
