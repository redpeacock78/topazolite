#lang racket

(require racket/match
         "rows.rkt"
         "type-equiv.rkt")

(provide compat?)

(define (record-compatible? sub-row sup-row)
  (for/and ([field (in-list sup-row)])
    (match field
      [(list label sup-type sup-mutability)
       (match (field-row-lookup sub-row label)
         [(list sub-type sub-mutability)
          (and (eq? sub-mutability sup-mutability)
               (case sup-mutability
                 [(imm) (compat? sub-type sup-type)]
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

;; VAR-002: Proof obligation は反変の集合包含。φ は exact 一致で照合する。
;; member はリストか #f を返すため、rackunit へ渡る値を厳密な boolean に落とす。
(define (obligations-subset? sub-obligations sup-obligations)
  (for/and ([obligation (in-list sub-obligations)])
    (and (member obligation sup-obligations) #t)))

;; VAR-001: 引数反変・返り値共変・引数個数一致。
(define (nfn-compatible? sub-parameters sub-return sub-row sub-obligations
                         sup-parameters sup-return sup-row sup-obligations)
  (and (= (length sub-parameters) (length sup-parameters))
       (for/and ([sub-parameter (in-list sub-parameters)]
                 [sup-parameter (in-list sup-parameters)])
         (compat? sup-parameter sub-parameter))
       (compat? sub-return sup-return)
       (effect-row-subset? sub-row sup-row)
       (obligations-subset? sub-obligations sup-obligations)))

(define (compat? sub sup)
  (match* (sub sup)
    [('Never _) #t]
    [(`(Record ,sub-row) `(Record ,sup-row))
     (record-compatible? sub-row sup-row)]
    [(`(Owned ,sub-type) `(Owned ,sup-type))
     (type-equiv? sub-type sup-type)]
    [(`(NFn ,sub-parameters ,sub-return ,sub-row ,sub-obligations)
      `(NFn ,sup-parameters ,sup-return ,sup-row ,sup-obligations))
     (nfn-compatible? sub-parameters sub-return sub-row sub-obligations
                      sup-parameters sup-return sup-row sup-obligations)]
    [(_ _) (type-equiv? sub sup)]))
