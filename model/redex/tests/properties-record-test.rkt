#lang racket
(require rackunit
         redex/reduction-semantics
         "../compat.rkt"
         "../gen.rkt"
         "../lang.rkt"
         "../type-equiv.rkt"
         "properties-test.rkt")

; TYP-003: 予約基本型（Int）と予約 Narrative（Proof φ）は structural matching の対象外。
; compat? の全域 dispatch で Record 枝に入らず type-equiv? 分岐のみを通るため、compat? は
; type-equiv? と一致する（List など閉じた型ではなく、予約型そのもので固定する）。
(check-equal? (compat? 'Int 'Int) (type-equiv? 'Int 'Int))
(check-equal? (compat? '(Proof ValidNarrativeTrait) '(Proof ValidNarrativeTrait))
              (type-equiv? '(Proof ValidNarrativeTrait) '(Proof ValidNarrativeTrait)))
(check-false (compat? '(Proof ValidNarrativeTrait) '(Proof TypeNarrativeCap)))

; 互換性と型同値の分離: 型同値でない record が互換になりうる
(check-true  (compat? '(Record ((a Int imm) (b Bool imm))) '(Record ((a Int imm)))))
; 逆向きは不可（非対称）
(check-false (compat? '(Record ((a Int imm))) '(Record ((a Int imm) (b Bool imm)))))

; source が Record 型または Rec 項を含むかを判定する Racket tree walker。
; 評価文脈 C は G2gen／UCore に存在しないため redex-match は使わず、s 式を辿る。
; Recur は 'Rec とも 'Record とも一致しないので誤検出しない。
(define (contains-record? t)
  (cond [(and (pair? t) (memq (car t) '(Rec Record))) #t]
        [(pair? t) (or (contains-record? (car t)) (contains-record? (cdr t)))]
        [else #f]))

(define limits (read-bounds))

; 既存 bounded-check（properties-test.rkt:287）と同じ harness を維持する G2 版。
(define-syntax-rule (bounded-check-g2 test-name pattern property)
  (test-case test-name
    (define counts (make-search-counts limits))
    (define record-accepted (box 0))
    (define result
      (call-with-search-seed
       limits
       (lambda ()
         (redex-check
          G2gen pattern #:ad-hoc
          (begin
            (note-accepted! counts)
            (when (contains-record? (term pattern))
              (set-box! record-accepted (add1 (unbox record-accepted))))
            (property (term pattern)))
          #:attempts (bounds-attempts limits)
          #:attempt-size (lambda (_attempt) (bounds-term-depth limits))
          #:prepare (lambda (source) (prepare-elaborable counts source))
          #:print? #f))))
    (check-equal? result #t)
    (check-true (positive? (search-counts-accepted counts)))
    (check-true (positive? (unbox record-accepted)))
    (printf "~a: attempts=~a accepted=~a record-accepted=~a discard=~a seed=~a\n"
            test-name
            (bounds-attempts limits)
            (search-counts-accepted counts)
            (unbox record-accepted)
            (search-counts-discarded counts)
            (bounds-seed limits))))

; 7 性質を各々固有の nonterminal で回す。1 個の共通 counter で代表させない。
(bounded-check-g2 "property 1 preservation (G2)"          g          preservation-g2?)
(bounded-check-g2 "property 2 progress (G2)"              g          progress-g2?)
(bounded-check-g2 "property 3 origin integrity (G2)"      g          origin-integrity-g2?)
(bounded-check-g2 "property 4 boundary safety (G2)"       g-boundary boundary-safe-g2?)
(bounded-check-g2 "property 5 TypeRep provenance (G2)"    g-type     type-info-integrity-g2?)
(bounded-check-g2 "property 6 conservative analysis (G2)" g-analysis conservative-analysis-g2?)
(bounded-check-g2 "property 7 affine safety (G2)"         g-own      affine-safety-g2?)
