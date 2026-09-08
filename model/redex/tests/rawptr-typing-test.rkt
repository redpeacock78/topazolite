#lang racket

(require rackunit
         "../region.rkt"
         "../borrow.rkt"
         "../search.rkt"
         "../typing.rkt")

;; borrow-test.rkt と同じ形で Λ を組む。借用を含む項は region IR が無いと
;; borrow-unknown-owner-region で落ちる。
(define (Λ-of ir) (region-ctx ir '() (hash) (hash)))

(define (check-core core)
  (define ir (build-region-ir core))
  (type-of/raw core '() '() '() (Λ-of ir)))

(define (key-of result)
  (match result
    [(list 'fail key _ ...) key]
    [_ #f]))

(define (type-of-ok result)
  (match result
    [(list 'ok (list type _row)) type]
    [_ #f]))

(define (row-of-ok result)
  (match result
    [(list 'ok (list _type row)) row]
    [_ #f]))

;; 可変借用を 1 つ作る最小の項。
(define (in-scope body)
  `(Scope ()
     (Let (x let (Owned Res)) (resource 1) ,body)))

;; AddressOf は可変借用から pointer を作り、6 引数を生成源へ固定する。
(test-case "AddressOf の 6 引数は生成源へ固定される"
  (define result (check-core (in-scope '(AddressOf (BorrowMut x)))))
  (check-equal? (type-of-ok result)
                '(RawPtr Res Mut NonNull (Align 1)
                         (AddrSpace native) (Prov owned))))

(test-case "AddressOf は共有借用を受け取らない"
  (check-equal?
   (key-of (check-core (in-scope '(AddressOf (Borrow x)))))
   'address-of-non-mut-borrow))

;; raw 操作は Unsafe の外では型が付かない。
(test-case "raw 操作は Unsafe の外で落ちる"
  (for ([body (in-list '((RawLoad (AddressOf (BorrowMut x)))
                         (PtrOffset (AddressOf (BorrowMut x)) 1)))])
    (check-equal? (key-of (check-core (in-scope body)))
                  'unsafe-outside-boundary
                  (format "~s" body)))
  ;; Res の欄へ Int を書くと型不一致が先に発火するため、payload と同型の
  ;; Res を Read して渡す。
  (check-equal?
   (key-of
    (check-core
     '(Scope ()
        (Let (x let (Owned Res)) (resource 1)
          (Let (y let (Owned Res)) (resource 2)
            (RawStore (AddressOf (BorrowMut x)) (Read (Borrow y))))))))
   'unsafe-outside-boundary))

;; Const の pointer への store は型検査が落とす。Const の pointer を作る
;; 項が本サイクルに無いため、切り出した述語を直に呼ぶ。
(test-case "RawStore の第一引数は Mut に限る"
  (define (target-key type)
    (let/ec escape
      (raw-store-target-check type (lambda (key _node) (escape key)))
      #f))
  (check-equal?
   (target-key '(RawPtr Res Mut NonNull (Align 1)
                        (AddrSpace native) (Prov owned)))
   #f)
  (check-equal?
   (target-key '(RawPtr Res Const NonNull (Align 1)
                        (AddrSpace native) (Prov owned)))
   'rawstore-const-pointer)
  (check-equal? (target-key 'Int) 'ptr-non-pointer))

(test-case "PtrOffset の第二引数は Int に限る"
  (check-equal?
   (key-of (check-core
            (in-scope '(PtrOffset (AddressOf (BorrowMut x)) unit))))
   'ptr-offset-non-int))

;; 各操作が要求する obligation の集合。
(test-case "obligation の集合"
  (check-equal? (raw-obligations '(AliveAllocation InBounds) 'Int)
                '((PtrProp AliveAllocation Int) (PtrProp InBounds Int)))
  (check-equal? (length (raw-load-obligation-ids)) 6)
  (check-equal? (length (raw-store-obligation-ids)) 5)
  (check-equal? (length (ptr-offset-obligation-ids)) 2)
  ;; store は未初期化の領域を初期化する操作でもあるため Initialized を求めない。
  (check-false (memq 'Initialized (raw-store-obligation-ids)))
  (check-false (memq 'Writable (raw-load-obligation-ids))))

;; PtrProp は validator 表に無く Γ-pc0 から暗黙充足されない。
(test-case "PtrProp は Γ-pc0 から暗黙充足されない"
  (check-false (obligations-dischargeable? '((PtrProp NonNull Int)) Γ-pc0))
  ;; 既存の validator 表にある命題は充足できる。対照として置く。
  (check-true (obligations-dischargeable? '() Γ-pc0)))

(test-case "RawStore の値は payload と互換でなければならない"
  (check-equal?
   (key-of
    (check-core
     '(Scope ()
        (Let (x let (Owned Res)) (resource 1)
          (RawStore (AddressOf (BorrowMut x)) 7)))))
   'rawstore-type-mismatch))

;; 許可集合から外れた RawPtr を作る項が本サイクルに無いため、
;; raw-store-target-check と同じく pointer-parts を直に呼ぶ。
(test-case "pointer-parts は成分違いを分類する"
  (define (parts-key type)
    (let/ec escape
      (pointer-parts 'node type (lambda (key _node) (escape key)))
      #f))
  (define (ptr as prov)
    `(RawPtr Res Mut NonNull (Align 1) ,as ,prov))
  (check-equal? (parts-key (ptr '(AddrSpace native) '(Prov owned))) #f)
  (check-equal? (parts-key (ptr '(AddrSpace gpu) '(Prov owned)))
                'invalid-address-space)
  (check-equal? (parts-key (ptr '(AddrSpace native) '(Prov native)))
                'invalid-provenance)
  (check-equal? (parts-key '(RawPtr Res Mut NonNull (Align 0)
                                    (AddrSpace native) (Prov owned)))
                'ptr-malformed)
  (check-equal? (parts-key 'Int) 'ptr-non-pointer))
