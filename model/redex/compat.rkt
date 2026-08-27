#lang racket

(require racket/match
         "erase.rkt"
         "policy.rkt"
         "rows.rkt"
         "search.rkt"
         "type-equiv.rkt")

(provide compat? check-compat-return)

;; ROW-002/ROW-005: field の可変性は一致ではなく互換で照合する。
;; imm を要求する位置には mut field を渡せる。書き込み能力を捨てる方向であり、
;; その位置からは読み出しだけが可能なため、他の枝が期待する狭い型を破れない。
;; 逆方向は能力を増やすため許さない。mut を要求する位置の field 型は、読みと
;; 書きの双方に使われるため type-equiv? の不変一致に留める。
(define (record-compatible? sub-row sup-row gamma-pc region-relation)
  (for/and ([field (in-list sup-row)])
    (match field
      [(list label sup-type sup-mutability)
       (match (field-row-lookup sub-row label)
         [(list sub-type sub-mutability)
          (and (memq sub-mutability '(imm mut))
               (case sup-mutability
                 [(imm) (compat?/impl sub-type sup-type gamma-pc region-relation)]
                 [(mut) (and (eq? sub-mutability 'mut)
                             (type-equiv? sub-type sup-type))]
                 [else #f]))]
         [_ #f])]
      [_ #f])))

;; VAR-002: latent effect は共変の集合包含。ラベル同一性は row-equiv? と
;; 同じ effect-equiv? を使い、Yield/Return payload の表記揺れを同一視する。
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

;; VAR-001: 引数反変・返り値共変・引数個数一致。
(define (nfn-compatible? sub-parameters sub-return sub-row sub-obligations
                         sup-parameters sup-return sup-row sup-obligations
                         gamma-pc region-relation)
  (and (= (length sub-parameters) (length sup-parameters))
       (for/and ([sub-parameter (in-list sub-parameters)]
                 [sup-parameter (in-list sup-parameters)])
         (compat?/impl sup-parameter sub-parameter gamma-pc region-relation))
       (compat?/impl sub-return sup-return gamma-pc region-relation)
       (effect-row-subset? sub-row sup-row)
       (obligations-subset? sub-obligations sup-obligations gamma-pc)))

;; gamma-pc の既定は空。そのとき obligations-subset? は集合包含だけを見るため、
;; G2c までの挙動と一致する。
(define (compat?/impl sub sup [gamma-pc '()] [region-relation equal?])
  (check-spanless! 'compat? sub)
  (check-spanless! 'compat? sup)
  ;; Union は節順に預けず、sub の各要素が sup のいずれかと互換かで判定する。
  (if (or (union? sub) (union? sup))
      (for/and ([sub-member (in-list (union-members sub))])
        (for/or ([sup-member (in-list (union-members sup))])
          (compat?/impl sub-member sup-member gamma-pc region-relation)))
      (compat?/non-union sub sup gamma-pc region-relation)))

(define (union? type)
  (and (pair? type) (eq? (car type) 'Union)))

(define (compat?/non-union sub sup gamma-pc region-relation)
  (match* (sub sup)
    [('Never _) #t]
    [(`(Record ,sub-row) `(Record ,sup-row))
     (record-compatible? sub-row sup-row gamma-pc region-relation)]
    [(`(Owned ,sub-type) `(Owned ,sup-type))
     (type-equiv? sub-type sup-type)]
    [(`(Untrusted ,sub-payload) `(Untrusted ,sup-payload))
     (compat?/impl sub-payload sup-payload gamma-pc region-relation)]
    ;; RFN-001: φ は命題同値を要求し、ペイロード型だけ compat? で再帰する。
    ;; type-equiv? と同じ proposition-equiv? を使い、同値型の互換性を保つ。
    [(`(Refined ,sub-payload ,sub-proposition)
      `(Refined ,sup-payload ,sup-proposition))
     (and (proposition-equiv? sub-proposition sup-proposition)
          (compat?/impl sub-payload sup-payload gamma-pc region-relation))]
    [(`(NFn ,sub-parameters ,sub-return ,sub-row ,sub-obligations)
      `(NFn ,sup-parameters ,sup-return ,sup-row ,sup-obligations))
     (nfn-compatible? sub-parameters sub-return sub-row sub-obligations
                      sup-parameters sup-return sup-row sup-obligations
                      gamma-pc region-relation)]
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
          (compat?/impl sub-payload sup-payload gamma-pc region-relation))]
    ;; VAR-004。可変借用は書き込みの経路であり、region 欄も payload も
    ;; 不変である。region を共変にすると、書き込んだ値の region が宣言より
    ;; 短くなりうる。payload を広げると、書き込んだ値が元の場所の型に
    ;; 合わなくなる。
    [(`(BorrowedMut ,sub-payload ,sub-ρ) `(BorrowedMut ,sup-payload ,sup-ρ))
     (and (equal? sub-ρ sup-ρ)
          (type-equiv? sub-payload sup-payload))]
    [(_ _) (type-equiv? sub sup)]))

;; POL-002/VAR-002: 同値な二型は互換である。compat? は全域であり fail-closed
;; 返却を持たない。span 機構の包みは型の形の外にあり、全域性の対象ではないため
;; error で落とす。VariancePolicy は宣言と境界検査を提供する。変性規則そのものを差し替える
;; 機構は持たない。借用の region の変位は VAR-004 として本ファイルへ入れた。
(define (check-compat-return args returns)
  (match* (args returns)
    [((list sub sup _ ...) (list result))
     (and (boolean? result)
          (or (not (type-equiv? sub sup)) (eq? result #t)))]
    [(_ _) #f]))

(define compat?
  (policy-wrap 'VariancePolicy 'compat?
               compat?/impl
               check-compat-return))
