#lang racket

(require racket/match
         "rows.rkt"
         "search.rkt"
         "type-equiv.rkt")

(provide compat?)

(define (record-compatible? sub-row sup-row gamma-pc)
  (for/and ([field (in-list sup-row)])
    (match field
      [(list label sup-type sup-mutability)
       (match (field-row-lookup sub-row label)
         [(list sub-type sub-mutability)
          (and (eq? sub-mutability sup-mutability)
               (case sup-mutability
                 [(imm) (compat? sub-type sup-type gamma-pc)]
                 [(mut) (type-equiv? sub-type sup-type)]
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
                         gamma-pc)
  (and (= (length sub-parameters) (length sup-parameters))
       (for/and ([sub-parameter (in-list sub-parameters)]
                 [sup-parameter (in-list sup-parameters)])
         (compat? sup-parameter sub-parameter gamma-pc))
       (compat? sub-return sup-return gamma-pc)
       (effect-row-subset? sub-row sup-row)
       (obligations-subset? sub-obligations sup-obligations gamma-pc)))

;; gamma-pc の既定は空。そのとき obligations-subset? は集合包含だけを見るため、
;; G2c までの挙動と一致する。
(define (compat? sub sup [gamma-pc '()])
  ;; Union は節順に預けず、sub の各要素が sup のいずれかと互換かで判定する。
  (if (or (union? sub) (union? sup))
      (for/and ([sub-member (in-list (union-members sub))])
        (for/or ([sup-member (in-list (union-members sup))])
          (compat? sub-member sup-member gamma-pc)))
      (compat?/non-union sub sup gamma-pc)))

(define (union? type)
  (and (pair? type) (eq? (car type) 'Union)))

(define (compat?/non-union sub sup gamma-pc)
  (match* (sub sup)
    [('Never _) #t]
    [(`(Record ,sub-row) `(Record ,sup-row))
     (record-compatible? sub-row sup-row gamma-pc)]
    [(`(Owned ,sub-type) `(Owned ,sup-type))
     (type-equiv? sub-type sup-type)]
    [(`(Untrusted ,sub-payload) `(Untrusted ,sup-payload))
     (compat? sub-payload sup-payload gamma-pc)]
    ;; RFN-001: φ は命題同値を要求し、ペイロード型だけ compat? で再帰する。
    ;; type-equiv? と同じ proposition-equiv? を使い、同値型の互換性を保つ。
    [(`(Refined ,sub-payload ,sub-proposition)
      `(Refined ,sup-payload ,sup-proposition))
     (and (proposition-equiv? sub-proposition sup-proposition)
          (compat? sub-payload sup-payload gamma-pc))]
    [(`(NFn ,sub-parameters ,sub-return ,sub-row ,sub-obligations)
      `(NFn ,sup-parameters ,sup-return ,sup-row ,sup-obligations))
     (nfn-compatible? sub-parameters sub-return sub-row sub-obligations
                      sup-parameters sup-return sup-row sup-obligations
                      gamma-pc)]
    [(_ _) (type-equiv? sub sup)]))
