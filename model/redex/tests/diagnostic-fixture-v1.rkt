#lang racket

;; registry version 1 を出したときの (code phase key) の列である。
;; このファイルは変更しない。追加は新しい版の fixture を足す形で行い、
;; この列には触れない。
;;
;; code だけでなく phase と key まで凍結するのは、E-TYP-012 を残したまま
;; key を別の reason へ替える「意味の付け替え」を検出するためである。
;; title は凍結しない。文言の推敲は意味の付け替えではない。
;;
;; test の契約は包含のみである。ここにある組が registry から消えるか、
;; 改名されるか、番号を再利用されるか、指す対象が変わると落ちる。
;; fixture は後方互換の履歴であって第二の正典ではない。現在の code 集合は
;; model/redex/diagnostic.rkt の registry を読む。

(provide diagnostic-entries-v1)

(define diagnostic-entries-v1
  '(("E-SYN-001" elaborate invalid-branch)
    ("E-SYN-002" elaborate invalid-branch-binders)
    ("E-SYN-003" elaborate invalid-syntax)
    ("E-TYP-002" elaborate cannot-synthesize)
    ("E-TYP-003" elaborate constructor-needs-expected-type)
    ("E-TYP-004" elaborate eliminate-needs-expected-type)
    ("E-TYP-005" elaborate invalid-resolved-type)
    ("E-TYP-006" elaborate invalid-type-annotation)
    ("E-TYP-007" elaborate invalid-type-application)
    ("E-TYP-008" elaborate invalid-type-representation)
    ("E-TYP-009" elaborate invalid-type-spec)
    ("E-TYP-010" elaborate narrative-expression-needs-expected-type)
    ("E-TYP-011" elaborate non-normalizable-type)
    ("E-TYP-012" elaborate type-mismatch)
    ("E-TYP-013" elaborate unknown-type)
    ("E-TYP-014" elaborate unknown-type-spec)
    ("E-TYP-015" elaborate unsaturated-type)
    ("E-KND-001" elaborate invalid-kind)
    ("E-KND-002" elaborate kind-mismatch)
    ("E-EFF-001" elaborate invalid-effect-label)
    ("E-EFF-002" elaborate undeclared-function-effect)
    ("E-EFF-003" elaborate undeclared-recur-effect)
    ("E-RET-001" elaborate return-label-outside-boundary)
    ("E-RET-002" elaborate return-outside-boundary)
    ("E-OWN-001" elaborate drop-non-owned)
    ("E-OWN-002" elaborate move-non-owned)
    ("E-OWN-003" elaborate owned-constructor-field)
    ("E-OWN-004" elaborate owned-curry-argument)
    ("E-OWN-005" elaborate owned-function-capture)
    ("E-OWN-006" elaborate owned-function-parameter)
    ("E-OWN-007" elaborate owned-record-field)
    ("E-OWN-008" elaborate owned-recur-capture)
    ("E-OWN-009" elaborate owned-recur-parameter)
    ("E-OWN-010" elaborate owned-variable-requires-move)
    ("E-VAR-001" elaborate duplicate-parameter)
    ("E-VAR-002" elaborate unbound-variable)
    ("E-REC-001" elaborate duplicate-recur-binder)
    ("E-REC-002" elaborate unknown-recur-requires-partial)
    ("E-ARI-001" elaborate arity-mismatch)
    ("E-DAT-001" elaborate constructor-type-arity)
    ("E-DAT-002" elaborate constructor-type-mismatch)
    ("E-DAT-003" elaborate non-data-eliminate)
    ("E-DAT-004" elaborate non-exhaustive-eliminate)
    ("E-RCD-001" elaborate const-record-residual)
    ("E-RCD-002" elaborate duplicate-record-label)
    ("E-RCD-003" elaborate project-non-record)
    ("E-RCD-004" elaborate unknown-record-label)
    ("E-APP-001" elaborate apply-non-function)
    ("E-APP-002" elaborate curry-non-function)
    ("E-PRF-001" elaborate invalid-obligation)
    ("E-PRF-002" elaborate invalid-proposition)
    ("E-PRF-003" elaborate missing-type-narrative-capability)
    ("E-PRF-004" elaborate unsatisfied-proof-obligation)
    ("E-TYP-001" typing ill-typed)
    ("E-ORG-001" origins forged)
    ("E-LOW-001" lowering kernel-primitive)
    ("E-LOW-002" lowering trait-primitive)
    ("E-LOW-003" lowering unknown-core-form)
    ("E-LOW-004" lowering unknown-core-type)))
