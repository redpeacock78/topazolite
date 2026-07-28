#lang racket
(require rackunit "../search.rkt")

;; 判定表の命題と常在性の witness を持つ複数命題の Γ_pc を組む。
;; entry = (φ O cid sid pid hook)、束縛は (name entry)。
(define gamma
  (list (list 'typeNarrativeCap
              (list 'TypeNarrativeCap '(Reserved o-type-narrative)
                    'typeNarrativeCap 'root 'default '()))
        (list 'portWitness
              (list '(Prop ValidPort) '(Reserved o-valid-port)
                    'portWitness 'root 'default '()))
        (list 'presenceWitness
              (list '(Presence a) '(Reserved o-merge)
                    'presenceWitness 'root 'default '()))))

;; RFN-003: χ は判定表の命題を Finite に写す。
(check-eq? (default-classifier (make-goal '(Prop ValidPort)) gamma) 'Finite)
(check-eq? (default-classifier (make-goal '(Prop NonEmpty)) gamma) 'Finite)
(check-eq? (default-classifier (make-goal 'TypeNarrativeCap) gamma) 'Finite)
;; RFN-002: 常在性の命題は label ごとに無限個あるため、表引きではなく
;; shape 規則で Finite に写す。
(check-eq? (default-classifier (make-goal '(Presence a)) gamma) 'Finite)
(check-eq? (default-classifier (make-goal '(Presence zzz)) gamma) 'Finite)
;; 判定表に無い命題は Unknown のままである。
(check-eq? (default-classifier (make-goal '(Prop ValidHost)) gamma) 'Unknown)

;; RFN-003: project-goal は goal の命題に一致する候補だけを抽出する。
(check-equal? (map candidate-prop
                   (project-goal gamma '(root) (make-goal '(Prop ValidPort))))
              '((Prop ValidPort)))
(check-equal? (map candidate-prop
                   (project-goal gamma '(root) (make-goal '(Presence a))))
              '((Presence a)))
(check-equal? (project-goal gamma '(root) (make-goal '(Prop NonEmpty))) '())
;; scope 不可視の文脈からは何も抽出しない。
(check-equal? (project-goal gamma '() (make-goal '(Prop ValidPort))) '())

;; RFN-003: wf-context? は goal に依らず、entry ごとの整合だけを見る。
(check-true (wf-context? gamma))
(check-false
 (wf-context?
  (list (list 'forged
              (list '(Prop ValidPort) '(Reserved o-non-empty)
                    'forged 'root 'default '())))))

;; RFN-002/003: 複数命題が同居しても、それぞれの goal を discharge できる。
;; project ではなく project-goal で抽出するため、無関係な候補が wf を落とさない。
(check-true (obligations-dischargeable? '((Prop ValidPort)) gamma))
(check-true (obligations-dischargeable? '((Presence a)) gamma))
(check-true (obligations-dischargeable? '(TypeNarrativeCap) gamma))
(check-false (obligations-dischargeable? '((Prop NonEmpty)) gamma))
(check-true (obligations-dischargeable?
             '((Prop ValidPort) (Presence a) TypeNarrativeCap) gamma))

;; 発行者対応を満たさない entry が一つでもあれば文脈ごと落ちる。
(check-false
 (obligations-dischargeable?
  '((Prop ValidPort))
  (list (list 'portWitness
              (list '(Prop ValidPort) '(Reserved o-valid-port)
                    'portWitness 'root 'default '()))
        (list 'forged
              (list '(Prop NonEmpty) '(Reserved o-valid-port)
                    'forged 'root 'default '())))))

;; 同じ命題の候補が二つあれば Ambiguous になり discharge できない。
(check-false
 (obligations-dischargeable?
  '((Prop ValidPort))
  (list (list 'one (list '(Prop ValidPort) '(Reserved o-valid-port)
                         'one 'root 'default '()))
        (list 'two (list '(Prop ValidPort) '(Reserved o-valid-port)
                         'two 'root 'default '())))))
