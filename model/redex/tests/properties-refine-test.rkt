#lang racket

(require rackunit
         racket/match
         redex/reduction-semantics
         "../compat.rkt"
         "../gen.rkt"
         "../lang.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../search.rkt"
         "../type-equiv.rkt"
         "../typing.rkt"
         "../validators.rkt"
         "properties-test.rkt")

;; ---------------------------------------------------------------------------
;; §7.1 決定的回帰: δ ステップの Preservation
;; ---------------------------------------------------------------------------

(test-case "RFN-001: validate 成功の Preservation"
  (check-true (preservation-g2? '(Apply validPort (Apply untrustedInt 8080)))))

(test-case "RFN-001: validate 失敗の Preservation"
  (check-true
   (preservation-g2? '(Apply validPort (Apply untrustedInt 70000))))
  (check-true
   (preservation-g2? '(Apply nonEmpty (Apply untrustedString "")))))

(test-case "RFN-001: 導入 primitive の Preservation"
  (check-true (preservation-g2? '(Apply untrustedInt 8080)))
  (check-true (preservation-g2? '(Apply untrustedString "localhost"))))

(define unrefine-source
  '(Apply (Fn () Int ()
            (Eliminate (Apply validPort (Apply untrustedInt 8080))
              ((ok (p) -> (Apply unrefinePort p))
               (ng (m) -> 0))))))

(test-case "RFN-001: 射影 primitive の Preservation"
  (check-true (preservation-g2? unrefine-source))
  (check-true (progress-g2? unrefine-source))
  (check-true (origin-integrity-g2? unrefine-source)))

;; ---------------------------------------------------------------------------
;; §7.1 決定的回帰: 初期 artifact 検証の層
;; ---------------------------------------------------------------------------

(define (verify-initial core) (term (verify-initial-origins ,R0 ,core)))
(define (verify core) (term (verify-origins ,R0 ,core)))

(define port-witness '(ProofRep (Reserved o-valid-port) (Prop ValidPort)))
(define merge-witness '(ProofRep (Reserved o-merge) (Presence a)))

(test-case "RFN-001: 初期項に埋めた UVal と RVal は意味検査の前に落ちる"
  ;; 正規の origin と φ で手書きした RVal も、初期項に現れた時点で拒否される。
  (check-equal? (verify-initial `(RVal ,port-witness 8080))
                `(forged (RVal ,port-witness 8080)))
  (check-equal? (verify-initial '(UVal 8080)) '(forged (UVal 8080)))
  (check-equal? (verify-initial `(Let (x const Int) (RVal ,port-witness 8080) x))
                `(forged (RVal ,port-witness 8080))))

(test-case "RFN-002: 初期項に埋めた常在性 witness を拒否する"
  (check-equal? (verify-initial merge-witness) `(forged ,merge-witness)))

;; ---------------------------------------------------------------------------
;; §7.1 決定的回帰: 到達状態検証の層
;; ---------------------------------------------------------------------------

(test-case "RFN-003: User origin の witness を載せた RVal を拒否する"
  (define forged `(RVal (ProofRep User (Prop ValidPort)) 8080))
  (check-equal? (verify forged) `(forged ,forged)))

(test-case "RFN-003: 発行者対応に無い origin と φ の組を拒否する"
  (define forged
    `(RVal (ProofRep (Reserved o-non-empty) (Prop ValidPort)) 8080))
  (check-equal? (verify forged) `(forged ,forged))
  (define forged-add `(ProofRep (Reserved o-add) (Prop ValidPort)))
  (check-equal? (verify forged-add) `(forged ,forged-add)))

(test-case "RFN-001: ペイロードを付け替えた RVal を拒否する"
  ;; check に通らないペイロード。
  (check-equal? (verify `(RVal ,port-witness 70000))
                `(forged (RVal ,port-witness 70000)))
  ;; 表の τ と一致しないペイロード。
  (check-equal? (verify `(RVal ,port-witness "8080"))
                `(forged (RVal ,port-witness "8080"))))

;; ---------------------------------------------------------------------------
;; §7.1 決定的回帰: 発行者対応と出現許可の分離（局所検査との対）
;; ---------------------------------------------------------------------------

(define merge-context
  (list (list 'a (list '(Presence a) '(Reserved o-merge)
                       'a 'root 'default '()))))

(test-case "RFN-002/003: 同じ witness が局所検査は通り artifact では落ちる"
  ;; 発行者対応は満たす。
  (check-true (proof-issuer-ok? R0 '(Reserved o-merge) '(Presence a)))
  ;; 局所検査では候補 wf を通り Resolved になる。
  (check-true (obligations-dischargeable? '((Presence a)) merge-context))
  ;; 同じ witness を到達 configuration へ埋めると出現許可で落ちる。
  (check-equal? (verify merge-witness) `(forged ,merge-witness)))

;; ---------------------------------------------------------------------------
;; §7.1 決定的回帰: 型付けの層
;; ---------------------------------------------------------------------------

(test-case "RFN-001: 判定表に無い命題の validate 適用に型が付かない"
  (check-equal? (core-type-of '(Apply validHost (UVal "localhost")) '() '())
                'ill-typed))

(test-case "RFN-001: Owned を含むペイロードに型が付かない"
  (check-equal? (core-type-of '(UVal (resource 1)) '() '()) 'ill-typed)
  (check-equal? (core-type-of `(RVal ,port-witness (resource 1)) '() '())
                'ill-typed))

;; ---------------------------------------------------------------------------
;; §7.2 bounded counterexample search。seed は bounds に従い、各性質に vacuity
;; counter を置いて全経路の実効を確かめる。
;; ---------------------------------------------------------------------------

(define limits (read-bounds))
(define attempts (bounds-attempts limits))

(define (delta-result row payload)
  (define core
    `(Apply (PrimVal (Reserved ,(validator-oid row)) ,(validator-name row))
            (UVal ,payload)))
  (match (run-g2 (inject-g2 core) (bounds-fuel limits))
    [`(cfg ,result ,_H ,_Ω ,_θ) result]
    [other (fail-check (format "unexpected run-g2 result: ~s" other))]))

(test-case "RFN-001: 性質1 validate 健全性"
  (call-with-search-seed
   limits
   (lambda ()
     (define ok-count (box 0))
     (define ng-count (box 0))
     (for ([_i (in-range attempts)])
       (define row (random-validator-row))
       (define payload (random-payload-for row))
       (define result (delta-result row payload))
       (match result
         [`(Construct ,_ ok (RVal (ProofRep ,origin ,proposition) ,carried))
          (set-box! ok-count (add1 (unbox ok-count)))
          (check-true ((validator-check row) payload))
          (check-equal? carried payload)
          (check-equal? proposition (validator-proposition row))
          (check-equal? origin `(Reserved ,(validator-oid row)))]
         [`(Construct ,_ ng ,message)
          (set-box! ng-count (add1 (unbox ng-count)))
          (check-false ((validator-check row) payload))
          (check-equal? message
                        (validator-error-message (validator-name row)))]
         [_ (fail-check (format "unexpected δ result: ~s" result))]))
     (check-true (positive? (unbox ok-count)))
     (check-true (positive? (unbox ng-count)))
     (printf "validate soundness: attempts=~a ok=~a ng=~a seed=~a\n"
             attempts (unbox ok-count) (unbox ng-count)
             (bounds-seed limits)))))

(test-case "RFN-002: 性質2 merge witness 健全性"
  (call-with-search-seed
   limits
   (lambda ()
     (define (expected-field-witnesses rows label)
       (define fields
         (for/list ([row (in-list rows)])
           (assoc label row)))
       (cond
         [(not (andmap values fields)) '()]
         [else
          (define first-field (first fields))
          (define mutability (third first-field))
          (define same-mutability?
            (for/and ([field (in-list (rest fields))])
              (eq? (third field) mutability)))
          (define normalized-types
            (map normalize-type (map second fields)))
          (define distinct-types
            (and (andmap values normalized-types)
                 (sort-then-dedup normalized-types)))
          (cond
            [(or (not same-mutability?) (not distinct-types)) '()]
            [(null? (rest distinct-types))
             (list `(Presence ,label))]
            [(eq? mutability 'imm)
             (cons `(Presence ,label)
                   (for/list ([type (in-list distinct-types)])
                     `(FieldType ,label ,type)))]
            [else '()])]))
     (define issued-count (box 0))
     (define dropped-count (box 0))
     (for ([_i (in-range attempts)])
       (define rows (random-branch-rows))
       (define types (for/list ([row (in-list rows)]) `(Record ,row)))
       (define-values (merged witnesses) (merge-record-types types))
       (match-define `(Record ,merged-row) merged)
       (define issued
         (for/list ([binding (in-list witnesses)])
           (entry-phi (second binding))))
       (define expected-issued
         (append-map
          (lambda (field)
            (expected-field-witnesses rows (first field)))
          (sort (first rows) symbol<? #:key first)))
       (check-equal? issued expected-issued)
       (define presence-issued
         (filter (lambda (proposition)
                   (match proposition
                     [`(Presence ,_) #t]
                     [_ #f]))
                 issued))
       ;; 過剰発行が無い: 3 分類で残る field にだけ Presence が立つ。
       (for ([proposition (in-list presence-issued)])
         (match-define `(Presence ,label) proposition)
         (set-box! issued-count (add1 (unbox issued-count)))
         (check-true
          (and (member `(Presence ,label)
                       (expected-field-witnesses rows label))
               #t)))
       ;; 過少発行が無い: merge 規則で残る field には必ず Presence が立つ。
       (for ([field (in-list (first rows))])
         (define label (first field))
         (define expected
           (expected-field-witnesses rows label))
         (cond
           [(member `(Presence ,label) expected)
            (check-true
             (and (member `(Presence ,label) presence-issued) #t))]
           [else
            (set-box! dropped-count (add1 (unbox dropped-count)))
            (check-false
             (member `(Presence ,label) presence-issued))]))
       ;; W を局所文脈として合流すると、各 witness の goal が discharge できる。
       (check-true (wf-context? witnesses))
       (check-true (merge-witnesses-dischargeable? types issued))
       (check-equal? (length merged-row) (length presence-issued)))
     (check-true (positive? (unbox issued-count)))
     (check-true (positive? (unbox dropped-count)))
     (printf "merge witness: attempts=~a issued=~a dropped=~a seed=~a\n"
             attempts (unbox issued-count) (unbox dropped-count)
             (bounds-seed limits)))))

;; 大域候補文脈。判定表の各命題の witness を一つずつ持つ。
(define global-context
  (for/list ([row (in-list validator-table)])
    (list (validator-name row)
          (list (validator-proposition row)
                `(Reserved ,(validator-oid row))
                (validator-name row) 'root 'default '()))))

;; 判定表の一部だけを持つ候補文脈。global-context は全命題を持つため生成した
;; 組がすべて受理され、性質3 の拒否側を探索が一度も踏まない。片方だけを持つ
;; 文脈を並べて、拒否側も探索で踏ませる。
(define partial-context (list (first global-context)))

(define (nfn obligations) `(NFn (Int) Int () ,obligations))

(test-case "RFN-003: Γ_pc⁰ は G1 の命題を候補の有無で分ける"
  (check-true (compat? (nfn '(TypeNarrativeCap)) (nfn '()) Γ-pc0))
  (check-false (compat? (nfn '(ValidNarrativeTrait)) (nfn '()) Γ-pc0)))

(test-case "RFN-003: 性質3 discharge 互換の方向健全性"
  (call-with-search-seed
   limits
   (lambda ()
     (define accepted-count (box 0))
     (define rejected-count (box 0))
     (for ([_i (in-range attempts)])
       (define sub-obligations (random-obligation-subset))
       (define sup-obligations (random-obligation-subset))
       (define dischargeable?
         (for/and ([proposition (in-list sub-obligations)])
           (or (and (member proposition sup-obligations) #t)
               (obligations-dischargeable? (list proposition)
                                           global-context))))
       (define result
         (compat? (nfn sub-obligations) (nfn sup-obligations)
                  global-context))
       (check-equal? result dischargeable?)
       (when result
         (set-box! accepted-count (add1 (unbox accepted-count))))
       ;; 同じ組を片方の witness しか持たない文脈で見る。sup に無い
       ;; (Prop NonEmpty) を sub が持つ組が拒否側へ落ちる。
       (define partial-dischargeable?
         (for/and ([proposition (in-list sub-obligations)])
           (or (and (member proposition sup-obligations) #t)
               (obligations-dischargeable? (list proposition)
                                           partial-context))))
       (define partial-result
         (compat? (nfn sub-obligations) (nfn sup-obligations)
                  partial-context))
       (check-equal? partial-result partial-dischargeable?)
       (unless partial-result
         (set-box! rejected-count (add1 (unbox rejected-count))))
       ;; Γ_pc⁰ にも Q_sup にも無い φ を持つ組は必ず拒否される。
       (check-false
        (compat? (nfn (cons '(Prop ValidHost) sub-obligations))
                 (nfn sup-obligations)
                 global-context)))
     (check-true (positive? (unbox accepted-count)))
     (check-true (positive? (unbox rejected-count)))
     (printf "discharge direction: attempts=~a accepted=~a rejected=~a seed=~a\n"
             attempts (unbox accepted-count) (unbox rejected-count)
             (bounds-seed limits)))))

(test-case "RFN-003: 性質4 無関係候補の weakening"
  (call-with-search-seed
   limits
   (lambda ()
     (define preserved-count (box 0))
     (for ([_i (in-range attempts)])
       (define sub-obligations (random-obligation-subset))
       (define base
         (list (list 'portWitness
                     (list '(Prop ValidPort) '(Reserved o-valid-port)
                           'portWitness 'root 'default '()))))
       (define accepted? (compat? (nfn sub-obligations) (nfn '()) base))
       (when accepted?
         (set-box! preserved-count (add1 (unbox preserved-count)))
         ;; goal と異なる命題の候補を足しても受理は保たれる。
         (check-true
          (compat? (nfn sub-obligations) (nfn '())
                   (cons (list 'other
                               (list '(Prop NonEmpty) '(Reserved o-non-empty)
                                     'other 'root 'default '()))
                         base)))
         ;; 候補同一性で同一視される複製を足しても受理は保たれる。
         (check-true
          (compat? (nfn sub-obligations) (nfn '())
                   (cons (list 'copy
                               (list '(Prop ValidPort) '(Reserved o-valid-port)
                                     'portWitness 'root 'default '()))
                         base)))))
     (check-true (positive? (unbox preserved-count)))
     (printf "weakening: attempts=~a preserved=~a seed=~a\n"
             attempts (unbox preserved-count) (bounds-seed limits)))))

;; PSR-002 の帰結として、同じ goal の別 identity 候補を足すと一意性が壊れて
;; Ambiguous になり、採択が落ちる。単調性が一般には成り立たないことを決定的に
;; 固定する。
(test-case "RFN-003: 同一 goal の別 identity 候補は受理を落とす"
  (define base
    (list (list 'portWitness
                (list '(Prop ValidPort) '(Reserved o-valid-port)
                      'portWitness 'root 'default '()))))
  (check-true (compat? (nfn '((Prop ValidPort))) (nfn '()) base))
  (check-false
   (compat? (nfn '((Prop ValidPort))) (nfn '())
            (cons (list 'another
                        (list '(Prop ValidPort) '(Reserved o-valid-port)
                              'another 'root 'default '()))
                  base))))

;; G2c の compat? を凍結した参照述語。拡張後の実装を呼ばない独立実装である。
;; obligation は完全一致包含だけを見る。Owned は最後の type-equiv? が構造的に
;; 判定するため、専用の節を置かなくても G2c と一致する。
(define (g2c-compat? sub sup)
  (match* (sub sup)
    [('Never _) #t]
    [(`(Record ,sub-row) `(Record ,sup-row))
     (for/and ([field (in-list sup-row)])
       (match-define (list label sup-type sup-mutability) field)
       (match (assoc label sub-row)
         [(list _ sub-type sub-mutability)
          (and (eq? sub-mutability sup-mutability)
               (case sup-mutability
                 [(imm) (g2c-compat? sub-type sup-type)]
                 [(mut) (type-equiv? sub-type sup-type)]
                 [else #f]))]
         [_ #f]))]
    [(`(NFn ,sub-parameters ,sub-return ,sub-row ,sub-obligations)
      `(NFn ,sup-parameters ,sup-return ,sup-row ,sup-obligations))
     (and (= (length sub-parameters) (length sup-parameters))
          (for/and ([sub-parameter (in-list sub-parameters)]
                    [sup-parameter (in-list sup-parameters)])
            (g2c-compat? sup-parameter sub-parameter))
          (g2c-compat? sub-return sup-return)
          (for/and ([label (in-list sub-row)])
            (for/or ([sup-label (in-list sup-row)])
              (effect-equiv? label sup-label)))
          (for/and ([obligation (in-list sub-obligations)])
            (and (member obligation sup-obligations) #t)))]
    [(_ _) (type-equiv? sub sup)]))

(test-case "RFN-003: 性質5 G2c 後方互換"
  (call-with-search-seed
   limits
   (lambda ()
     (define true-count (box 0))
     (define false-count (box 0))
     (for ([_i (in-range attempts)])
       (define left (random-variance-type 3))
       (define right (random-variance-type 3))
       (define expected (g2c-compat? left right))
       (check-equal? (compat? left right) expected)
       (if expected
           (set-box! true-count (add1 (unbox true-count)))
           (set-box! false-count (add1 (unbox false-count))))
       ;; narrow 方向は構成的に受理される組であり、こちらも一致する。
       (define narrowed (narrow-variance-type right))
       (check-equal? (compat? narrowed right) (g2c-compat? narrowed right)))
     (check-true (positive? (unbox true-count)))
     (check-true (positive? (unbox false-count)))
     (printf "g2c compatibility: attempts=~a true=~a false=~a seed=~a\n"
             attempts (unbox true-count) (unbox false-count)
             (bounds-seed limits)))))
