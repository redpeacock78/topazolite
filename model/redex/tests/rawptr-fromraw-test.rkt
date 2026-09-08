#lang racket

(require rackunit
         "../region.rkt"
         "../borrow.rkt"
         "../typing.rkt")

(define (Λ-of ir) (region-ctx ir '() (hash) (hash)))

(define (key-of result)
  (match result
    [(list 'fail key _ ...) key]
    [_ #f]))

;; from-raw-ptr-result-type の棄却を単体で取る。fail を渡す形は
;; payload-borrows-traceable? の先例に揃えてある。
(define (result-type type region)
  (let/ec escape
    (from-raw-ptr-result-type type region
                              (lambda (key _node) (escape key)))))

(define (ptr payload ptrmut [nul 'NonNull]
             [as '(AddrSpace native)] [prov '(Prov owned)])
  `(RawPtr ,payload ,ptrmut ,nul (Align 1) ,as ,prov))

;; lifetime、alignment、validity の Proof を要求する。
(test-case "FromRawPtr の obligation は 5 つである"
  (define ids (from-raw-ptr-obligation-ids))
  (check-equal? (length ids) 5)
  (for ([id (in-list '(LifetimeValid Aligned Initialized
                       AliveAllocation NonNull))])
    (check-true (and (memq id ids) #t) (format "~a" id))))

;; ptrmut で Borrowed と BorrowedMut を作り分ける。
(test-case "ptrmut で借用の種を分ける"
  (check-equal? (result-type (ptr 'Res 'Const) '(RVar 0))
                '(Borrowed Res (RVar 0)))
  (check-equal? (result-type (ptr 'Res 'Mut) '(RVar 0))
                '(BorrowedMut Res (RVar 0))))

;; 入力の nul は場合分けしない。Nullable からも構築を試みてよい。
(test-case "Nullable の pointer も受け取る"
  (check-equal? (result-type (ptr 'Int 'Const 'Nullable) '(RVar 0))
                '(Borrowed Int (RVar 0))))

;; 外部の allocation と native 以外の address space は落とす。
(test-case "provenance と address space を限る"
  (check-equal?
   (result-type (ptr 'Int 'Const 'NonNull '(AddrSpace native) '(Prov foreign))
                '(RVar 0))
   'from-raw-ptr-non-owned)
  (check-equal?
   (result-type (ptr 'Int 'Const 'NonNull '(AddrSpace js-buffer) '(Prov owned))
                '(RVar 0))
   'from-raw-ptr-non-native)
  (check-equal? (result-type 'Int '(RVar 0)) 'ptr-non-pointer))

;; region 注釈は fixture の IR から作る。region-counter は build-region-ir の
;; 呼び出しをまたいで戻らないため、IR を一度だけ作って region->rho で ρ を作り、
;; 同じ IR から組んだ Λ を type-of/raw へ渡す。
(define (fromraw-core ρ)
  `(Scope ()
     (Let (x let (Owned Res)) (resource 1)
       (FromRawPtr (AddressOf (BorrowMut x)) ,ρ))))

(define (unsafe-fromraw-core ρ)
  `(Scope ()
     (Let (x let (Owned Res)) (resource 1)
       (Unsafe (FromRawPtr (AddressOf (BorrowMut x)) ,ρ)))))

(define fromraw-ir (build-region-ir (fromraw-core 0)))
(define fromraw-Λ (Λ-of fromraw-ir))
(define fromraw-ρ
  (region->rho fromraw-ir (region-at fromraw-ir '(0 1))))

(define unsafe-fromraw-ir (build-region-ir (unsafe-fromraw-core 0)))
(define unsafe-fromraw-Λ (Λ-of unsafe-fromraw-ir))
(define unsafe-fromraw-ρ
  (region->rho unsafe-fromraw-ir (region-at unsafe-fromraw-ir '(0 1))))

;; FromRawPtr も Unsafe の外では落ちる。
(test-case "FromRawPtr は Unsafe の外で落ちる"
  (check-equal?
   (key-of (type-of/raw (fromraw-core fromraw-ρ) '() '() '() fromraw-Λ))
   'unsafe-outside-boundary))

;; unsafe.md §4.1。boundary の内側では通り、可変借用になる。
(test-case "FromRawPtr は Unsafe の内側で通る"
  (match (type-of/raw (unsafe-fromraw-core unsafe-fromraw-ρ)
                      '() '() '() unsafe-fromraw-Λ)
    [(list 'ok (list type _row))
     (check-equal? (first type) 'BorrowedMut
                   (format "~s" type))]
    [other (fail (format "受理されなかった: ~s" other))]))
