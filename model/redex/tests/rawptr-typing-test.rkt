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
;; 注釈と生成結果を Let で突き合わせ、続けて RawLoad まで通す。
(test-case "AddressOf の 6 引数は生成源へ固定される"
  (match (check-core
          (in-scope
           '(Unsafe
             (Let (p const (RawPtr Res Mut NonNull (Align 1)
                                    (AddrSpace native) (Prov owned)))
                  (AddressOf (BorrowMut x))
                  (RawLoad p)))))
    [(list 'ok (list type row))
     (check-equal? type 'Res)
     (check-false (memq 'Unsafe row))
     (check-false (memq 'Mutation row) "RawLoad は Mutation を出さない")]
    [other (fail (format "受理されなかった: ~s" other))]))

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

;; unsafe.md §4.1。boundary の内側では raw load が通る。
(test-case "RawLoad は Unsafe の内側で通る"
  (define result
    (check-core (in-scope '(Unsafe (RawLoad (AddressOf (BorrowMut x)))))))
  (check-equal? (type-of-ok result) 'Res))

;; unsafe.md §2.2。boundary の内側では raw store が Unit を返す。
(test-case "RawStore は Unit を返す"
  (define result
    (check-core
     `(Scope ()
        (Let (x let (Owned Res)) (resource 1)
          (Let (y let (Owned Res)) (resource 2)
            (Unsafe (RawStore (AddressOf (BorrowMut x))
                              (Read (Borrow y)))))))))
  (check-equal? (type-of-ok result) 'Unit))

;; PtrOffset の結果は RawPtr なので boundary の外へは出せない。
(test-case "PtrOffset の RawPtr は Unsafe の外へ出せない"
  (check-equal?
   (key-of
    (check-core
     (in-scope '(Unsafe (PtrOffset (AddressOf (BorrowMut x)) 1)))))
   'rawptr-escapes-unsafe))

;; unsafe.md §2.2 と §4.1。RawStore は Mutation を出し、境界の外まで残る。
;; Unsafe は境界で剥がれる。
(test-case "RawStore の Mutation は Unsafe 境界の外へ残る（unsafe.md §4.1）"
  (define row
    (row-of-ok
     (check-core
      `(Scope ()
         (Let (x let (Owned Res)) (resource 1)
           (Let (y let (Owned Res)) (resource 2)
             (Unsafe (RawStore (AddressOf (BorrowMut x))
                               (Read (Borrow y))))))))))
  (check-false (memq 'Unsafe row) "Unsafe は境界で剥がれる")
  (check-true (and (memq 'Mutation row) #t) "Mutation は境界を越えて残る"))
