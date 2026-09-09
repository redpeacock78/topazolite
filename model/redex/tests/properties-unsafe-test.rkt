#lang racket

(require rackunit racket/match
         "../gen.rkt"
         "../ptr-static.rkt"
         "../unsafe-gen.rkt"
         "../unsafe-oracle.rkt")

;; 性質 9。生成した G2 項の到達可能な実行の上で、raw 操作が Unsafe の内側に
;; あり、obligation が静的側と一致し、境界の外へ PtrVal が出ない。
(define (run-unsafe-search)
  (define limits (read-bounds))
  (define counters (make-ucounters))
  (define failures '())
  (define discarded 0)
  (define accepted 0)
  (define outside 0)
  (define ptr-offset-requests 0)
  (call-with-search-seed
   limits
   (lambda ()
     (for ([_i (in-range (bounds-attempts limits))])
       (define term (gen-unsafe-term (bounds-term-depth limits)))
       (match (prepare-unsafe-term term)
         [(list 'ok config sidecar)
          (when (for/or ([r (in-list (ptr-sidecar-requests sidecar))])
                  (eq? (ptr-request-kind r) 'ptr-offset))
            (set! ptr-offset-requests (add1 ptr-offset-requests)))
          ;; 型検査を通った項では、記録されたすべての出現が Unsafe の内側にある。
          ;; check-raw-obligations! は Γ-pc0 で解ける obligation を境界の外でも
          ;; 通すため、この主張はその判定の言い換えではない。
          ;; 記録されるのは境界を要求する 4 つ（RawLoad、RawStore、PtrOffset、
          ;; FromRawPtr）である。AddressOf は記録しないため対象外である。
          (unless (for/and ([r (in-list (ptr-sidecar-requests sidecar))])
                    (ptr-request-unsafe? r))
            (set! outside (add1 outside)))
          (define outcome
            (check-unsafe-execution config sidecar
                                    (bounds-fuel limits) counters))
          (match outcome
            ['ok (set! accepted (add1 accepted))]
            ['discard (set! discarded (add1 discarded))]
            [(list 'fail reason detail)
             (set! failures (cons (list reason detail term) failures))])]
         ['discard (set! discarded (add1 discarded))]))))
  (list accepted discarded failures counters outside ptr-offset-requests))

(define search-result (run-unsafe-search))

(test-case "性質 9 の反例が無い"
  (check-equal? (third search-result) '()))

(test-case "受理した実行がある"
  (check-true (positive? (first search-result))))

(test-case "discard が上限を超えない"
  (check-true (< (second search-result)
                 (bounds-discard-limit (read-bounds)))))

(test-case "ptr-offset 以外のカウンタが非零"
  ;; G2m では自然数 path を作る規則が共有借用側にしかなく、
  ;; AddressOf は可変借用だけを受けるため R-PtrOffset は到達不能である。
  ;; その欄を無視せず、到達不能の事実を exact に固定する。
  (check-equal? (ucounters-zeros (fourth search-result)) '(ptr-offset)))

(test-case "型検査を通った項の raw 操作はすべて Unsafe の内側にある"
  (check-equal? (fifth search-result) 0))

(test-case "PtrOffset の静的要求は生成域に現れる"
  (check-true (positive? (sixth search-result))))
