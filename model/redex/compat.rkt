#lang racket

(require racket/match
         "erase.rkt"
         "policy.rkt"
         "rows.rkt"
         "search.rkt"
         "type-equiv.rkt")

(provide compat? tag-compat? tag-narrowing? reassign-narrowing?
         check-compat-return)

;; 部分型の不変位置では NFn の O を比較しない。
;; O 以外の型構造は type-equiv? のまま保ち、record の mut field、BorrowedMut、
;; fallback の不変位置で使う。Owned の payload は別の節で tag-narrowing? を使う。
;; NFn の引数・返り値・row・義務へ潜るため、ネストした関数型でも O だけが外れる。
(define (compat-erase-nfn-origins type)
  (match type
    [`(NFn ,parameters ,return-type ,in-row ,out-row ,obligations ,_origin)
     `(NFn ,(map compat-erase-nfn-origins parameters)
           ,(compat-erase-nfn-origins return-type)
           ,(map compat-erase-nfn-origins in-row)
           ,(map compat-erase-nfn-origins out-row)
           ,(map compat-erase-nfn-origins obligations)
           User)]
    [(? list?) (map compat-erase-nfn-origins type)]
    [_ type]))

(define (compat-type-equiv? left right)
  (type-equiv? (compat-erase-nfn-origins left)
               (compat-erase-nfn-origins right)))

;; ROW-002/ROW-005: field の可変性は一致ではなく互換で照合する。
;; imm を要求する位置には mut field を渡せる。書き込み能力を捨てる方向であり、
;; その位置からは読み出しだけが可能なため、他の枝が期待する狭い型を破れない。
;; 逆方向は能力を増やすため許さない。mut を要求する位置の field 型は、読みと
;; 書きの双方に使われるため、通常の compat? では type-equiv? を求める。
;; tag 保存互換では tag の狭まりを求める。
(define (record-compatible? sub-row sup-row gamma-pc region-relation recur invariant?)
  (for/and ([field (in-list sup-row)])
    (match field
      [(list label sup-type sup-mutability _ ...)
       (match (assoc label sub-row)
         [(and sub-field (list _ sub-type sub-mutability _ ...))
          (and (or (not (field-optional? sub-field))
                   (field-optional? field))
               (memq sub-mutability '(imm mut))
               (case sup-mutability
                 [(imm) (recur sub-type sup-type gamma-pc region-relation)]
                 [(mut) (and (eq? sub-mutability 'mut)
                             (invariant? sub-type sup-type))]
                 [else #f]))]
         [_ #f])]
      [_ #f])))

;; VAR-002: latent effect は共変の集合包含。εin へ反変で使う場合は呼出し側が
;; 引数順を入れ替える。ラベル同一性は row-equiv? と同じ effect-equiv? を使い、
;; Yield/Return payload の表記揺れを同一視する。
(define (effect-row-subset? sub-row sup-row)
  (for/and ([label (in-list sub-row)])
    (for/or ([sup-label (in-list sup-row)])
      (effect-equiv? label sup-label))))

;; VAR-002/RFN-003: Proof obligation は反変の集合包含であるが、候補文脈が
;; 既に witness を持つ義務は包含が無くても充足できる。discharge に使う文脈は
;; 呼び出し側が渡す大域の Γ_pc⁰ に限る。merge の W を混ぜると、その merge の
;; 外へ関数値が逃げたときに義務の根拠が消え、Preservation が壊れる。
;; 包含は proposition-equiv? で判定する。表記の違う同値命題を別物にしないが、
;; 正準鍵が作れない命題どうしは構文一致へ落ちるため、旧来の member と同じ強さを
;; 保つ。正準鍵を直接比べると #f どうしが一致して偽陽性になる。
(define (obligations-subset? sub-obligations sup-obligations gamma-pc)
  (for/and ([obligation (in-list sub-obligations)])
    (or (for/or ([sup-obligation (in-list sup-obligations)])
          (proposition-equiv? obligation sup-obligation))
        (obligations-dischargeable? (list obligation) gamma-pc))))

;; VAR-001: 引数反変・返り値共変・εin 反変・εout 共変・引数個数一致。
(define (nfn-compatible? sub-parameters sub-return sub-in sub-out sub-obligations
                         sup-parameters sup-return sup-in sup-out sup-obligations
                         gamma-pc region-relation recur)
  (and (= (length sub-parameters) (length sup-parameters))
       (for/and ([sub-parameter (in-list sub-parameters)]
                 [sup-parameter (in-list sup-parameters)])
         (recur sup-parameter sub-parameter gamma-pc region-relation))
       (recur sub-return sup-return gamma-pc region-relation)
       (effect-row-subset? sup-in sub-in)
       (effect-row-subset? sub-out sup-out)
       (obligations-subset? sub-obligations sup-obligations gamma-pc)))

(define (union? type)
  (and (pair? type) (eq? (car type) 'Union)))

(define (compat?/non-union sub sup gamma-pc region-relation recur invariant?)
  (match* (sub sup)
    [('Never _) #t]
    [(`(Record ,sub-row) `(Record ,sup-row))
     (record-compatible? sub-row sup-row gamma-pc region-relation recur invariant?)]
    [(`(Owned ,sub-type) `(Owned ,sup-type))
     ;; 一意な所有者は旧い view を同時に保てないため、tag を保つ payload widening
     ;; を通常の互換でも受理する。tag の無い値への新しい tag の追加は許さない。
     (tag-narrowing? sub-type sup-type)]
    [(`(Untrusted ,sub-payload) `(Untrusted ,sup-payload))
     (recur sub-payload sup-payload gamma-pc region-relation)]
    ;; RFN-001: φ は命題同値を要求し、ペイロード型だけ compat? で再帰する。
    ;; type-equiv? と同じ proposition-equiv? を使い、同値型の互換性を保つ。
    [(`(Refined ,sub-payload ,sub-proposition)
     `(Refined ,sup-payload ,sup-proposition))
     (and (proposition-equiv? sub-proposition sup-proposition)
          (recur sub-payload sup-payload gamma-pc region-relation))]
    [(`(NFn ,sub-parameters ,sub-return ,sub-in ,sub-out ,sub-obligations ,_sub-origin)
      `(NFn ,sup-parameters ,sup-return ,sup-in ,sup-out ,sup-obligations ,_sup-origin))
     (nfn-compatible? sub-parameters sub-return sub-in sub-out sub-obligations
                      sup-parameters sup-return sup-in sup-out sup-obligations
                      gamma-pc region-relation recur)]
    ;; 構成子が一致し、payload が互換であることを要求する。
    ;; Borrowed と BorrowedMut のあいだの暗黙の強化と弱化を認めない。
    ;; 弱化を認めると、可変借用を共有借用の位置へ渡しつつ元の可変借用が
    ;; 生き続ける抜けができる。
    ;; VAR-004。共有借用の region 欄は共変である。長く生きる借用は短く
    ;; 生きる借用の位置へ渡せる。包含の判定は region-relation へ預ける。
    ;; 既定の equal? のままなら、region 引数を書かない programme の判定は
    ;; 変わらない。payload の再帰へも同じ関係を渡す。渡さないと最上位で
    ;; だけ共変になり、1 段下で equal? に戻る。
    [(`(Borrowed ,sub-payload ,sub-ρ) `(Borrowed ,sup-payload ,sup-ρ))
     (and (region-relation sub-ρ sup-ρ)
          (recur sub-payload sup-payload gamma-pc region-relation))]
    ;; VAR-004。可変借用は書き込みの経路であり、region 欄も payload も
    ;; 不変である。region を共変にすると、書き込んだ値の region が宣言より
    ;; 短くなりうる。payload を広げると、書き込んだ値が元の場所の型に
    ;; 合わなくなる。
    [(`(BorrowedMut ,sub-payload ,sub-ρ) `(BorrowedMut ,sup-payload ,sup-ρ))
     (and (equal? sub-ρ sup-ρ)
          (compat-type-equiv? sub-payload sup-payload))]
    [(_ _) (compat-type-equiv? sub sup)]))

;; tag の狭まりでは Union の成分位置だけを緩める。
;; それ以外の型の形は compat-type-equiv? で閉じる。
(define (record-narrowing? actual-row expected-row)
  (field-row-equiv? actual-row expected-row tag-narrowing?))

(define (tag-narrowing? actual expected)
  (define a (normalize-type actual))
  (define e (normalize-type expected))
  (and a e
       (match* (a e)
         [('Never `(Union ,_ ,_)) #t]
         [(`(Union ,_ ,_) `(Union ,_ ,_))
          (for/and ([member (in-list (union-members a))])
            (for/or ([expected-member (in-list (union-members e))])
              (type-equiv? member expected-member)))]
         [(`(Record ,actual-row) `(Record ,expected-row))
          (record-narrowing? actual-row expected-row)]
         [(`(Owned ,actual-payload) `(Owned ,expected-payload))
          (tag-narrowing? actual-payload expected-payload)]
         [(`(Untrusted ,actual-payload) `(Untrusted ,expected-payload))
          (tag-narrowing? actual-payload expected-payload)]
         [(`(Refined ,actual-payload ,actual-proposition)
           `(Refined ,expected-payload ,expected-proposition))
          (and (proposition-equiv? actual-proposition expected-proposition)
               (tag-narrowing? actual-payload expected-payload))]
         [(_ _) (compat-type-equiv? a e)])))

;; Reassign の値の照合。期待が imm の欄に限り実際の mut を許す。
;; 欄の集合と optional の印、期待が mut の欄、Owned などの wrapper は
;; 従来の tag-narrowing? の制約を保つ。
(define (reassign-narrowing? actual expected)
  (define a (normalize-type actual))
  (define e (normalize-type expected))
  (and a e
       (match* (a e)
         [(`(Record ,actual-row) `(Record ,expected-row))
          (and (= (length actual-row) (length expected-row))
               (for/and ([field (in-list expected-row)])
                 (match field
                   [(list label type 'imm _ ...)
                    (define actual-field (assoc label actual-row))
                    (match (field-row-lookup actual-row label)
                      [(list actual-type actual-mutability)
                       (and actual-field
                            (memq actual-mutability '(imm mut))
                            (eq? (field-presence actual-field)
                                 (field-presence field))
                            (reassign-narrowing? actual-type type))]
                      [_ #f])]
                   [(list label type 'mut _ ...)
                    (define actual-field (assoc label actual-row))
                    (match (field-row-lookup actual-row label)
                      [(list actual-type actual-mutability)
                       (and actual-field
                            (eq? actual-mutability 'mut)
                            (eq? (field-presence actual-field)
                                 (field-presence field))
                            (tag-narrowing? actual-type type))]
                      [_ #f])]
                   [_ #f])))]
         [(_ _) (tag-narrowing? a e)])))

;; 通常の互換と tag 保存互換で再帰だけを切り替え、既存の compat? は保つ。
(define (compat?/impl/tag tag-mode? sub sup gamma-pc region-relation)
  (check-spanless! (if tag-mode? 'tag-compat? 'compat?) sub)
  (check-spanless! (if tag-mode? 'tag-compat? 'compat?) sup)
  (define (recur actual expected gamma relation)
    (compat?/impl/tag tag-mode? actual expected gamma relation))
  (define invariant?
    (if tag-mode? tag-narrowing? compat-type-equiv?))
  (cond
    [tag-mode?
     (cond
       [(union? sup)
        (or (eq? sub 'Never)
            (and (union? sub)
                 (for/and ([member (in-list (union-members sub))])
                   (for/or ([expected-member (in-list (union-members sup))])
                     (type-equiv? member expected-member)))))]
       [(union? sub) #f]
       [else
        (compat?/non-union sub sup gamma-pc region-relation recur invariant?)])]
    [(or (union? sub) (union? sup))
     (for/and ([sub-member (in-list (union-members sub))])
       (for/or ([sup-member (in-list (union-members sup))])
         (recur sub-member sup-member gamma-pc region-relation)))]
    [else
     (compat?/non-union sub sup gamma-pc region-relation recur invariant?)]))

(define (compat?/impl sub sup [gamma-pc '()] [region-relation equal?])
  (compat?/impl/tag #f sub sup gamma-pc region-relation))

(define (tag-compat? actual expected [gamma-pc '()] [region-relation equal?])
  (compat?/impl/tag #t actual expected gamma-pc region-relation))

;; POL-002/VAR-002: 同値な二型は互換である。compat? は全域であり fail-closed
;; 返却を持たない。span 機構の包みは型の形の外にあり、全域性の対象ではないため
;; error で落とす。VariancePolicy は宣言と境界検査を提供する。変性規則そのものを差し替える
;; 機構は持たない。借用の region の変位は VAR-004 として本ファイルへ入れた。
(define (check-compat-return args returns)
  (match* (args returns)
    [((list sub sup _ ...) (list result))
     (and (boolean? result)
          (or (not (compat-type-equiv? sub sup)) (eq? result #t)))]
    [(_ _) #f]))

(define compat?
  (policy-wrap 'VariancePolicy 'compat?
               compat?/impl
               check-compat-return))
