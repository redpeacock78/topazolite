#lang racket

(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../machine.rkt"
         "../origins.rkt"
         "../traits.rkt"
         "../gen.rkt"
         "../typing.rkt")

;; raw-steps-g2/named は (list 規則名 簡約後の config) の並びを返す。
;; 1 手であることも同時に確かめる。
(define (one-named config)
  (define steps (raw-steps-g2/named config))
  (check-equal? (length steps) 1 (format "1 手でない: ~s" config))
  (first steps))

(define (step-count config)
  (length (raw-steps-g2 config)))

;; Rec の欄の並びは (label m v) である（lang.rkt:259 の G2m の v の Rec）。
(define (rec-config core)
  (term (cfg ,core ((0 (Rec ((f0 mut 1) (f1 imm 2)))))
             ((0 Available)) () ())))

;; AddressOf と使用規則の型 guard 用に宣言型を持つ heap。
(define rec-type '(Record ((f0 Int mut) (f1 Int imm))))

(define (rec-config/declared core [owned-root? #f])
  (term (cfg ,core
             ((0 (Rec ((f0 mut 1) (f1 imm 2)))
                 (declared ,(if owned-root? `(Owned ,rec-type) rec-type))))
             ((0 Available)) () ())))

;; unsafe.md §2.3。Ω が Available でない場合の負例を取るための config。
(define (moved-config core)
  (term (cfg ,core
             ((0 (Rec ((f0 mut 1) (f1 imm 2))) (declared ,rec-type)))
             ((0 Moved)) () ())))

(define (pair-config core)
  (term (cfg ,core
             ((0 (Construct (Data Pair (Int Bool)) mkpair
                            1 (Construct Bool true))
                 (declared (Data Pair (Int Bool)))))
             ((0 Available)) () ())))

(define pair-ledger
  (make-trait-ledger
   canonical-trait-env
   #:data '((Pair (A B) ((mkpair ((Param A) (Param B))))))
   #:fail (lambda args (error 'test "unexpected ledger failure: ~s" args))))

(define (pointer fp type [ptrmut 'Mut] [nul 'NonNull]
                 [prov '(Prov owned)])
  `(PtrVal 0 ,fp
           (RawPtr ,type ,ptrmut ,nul (Align 1)
                   (AddrSpace native) ,prov)))

;; unsafe.md §2.3。R-AddressOf は可変借用から PtrVal を作る。
;; PtrVal は静的な RawPtr 型を実行時にも運ぶ。
(test-case "R-AddressOf は Mut の PtrVal を作る（unsafe.md §2.3）"
  (match-define (list name after)
    (one-named (rec-config/declared
                (term (AddressOf (BorrowMutRef 0 (f0) (RVar 0)))))))
  (check-equal? name 'R-AddressOf)
  (check-equal? (config-core after)
                (pointer '(f0) 'Int 'Mut)))

(test-case "R-AddressOf は Owned の宣言から payload 型を辿る"
  (match-define (list name after)
    (one-named (rec-config/declared
                (term (AddressOf (BorrowMutRef 0 (f0) (RVar 0)))) #t)))
  (check-equal? name 'R-AddressOf)
  (check-equal? (config-core after) (pointer '(f0) 'Int 'Mut)))

(test-case "宣言の無い heap では R-AddressOf が発火しない"
  (check-equal?
   (step-count (rec-config (term (AddressOf (BorrowMutRef 0 (f0) (RVar 0))))))
   0))

(test-case "PtrVal を含む構成を config typing と runtime-row が受理する"
  (define config
    (rec-config/declared `(Unsafe (RawLoad ,(pointer '(f0) 'Int 'Const)))))
  (define row (runtime-row config '() 'Int))
  (check-equal? row '())
  (check-true (config-ok? config '() 'Int row)))

;; unsafe.md §2.3。R-RawLoad は Const と Mut の両方で発火する。
(test-case "R-RawLoad は H の該当欄を読む（unsafe.md §2.3）"
  (for ([ptrmut (in-list '(Const Mut))])
    (match-define (list name after)
      (one-named (rec-config/declared
                  `(RawLoad ,(pointer '(f0) 'Int ptrmut)))))
    (check-equal? name 'R-RawLoad)
    (check-equal? (config-core after) (term 1))))

(test-case "R-RawLoad は pointee 型が path 型と一致しなければ発火しない"
  (check-equal?
   (call-with-trait-ledger
    pair-ledger
    (lambda ()
      (step-count (pair-config `(RawLoad ,(pointer '(1) 'Int 'Const))))))
   0))

;; unsafe.md §2.3。R-RawStore は Mut の PtrVal に限る。
(test-case "R-RawStore は H の該当欄を書く（unsafe.md §2.3）"
  (match-define (list name after)
    (one-named (rec-config/declared
                `(RawStore ,(pointer '(f0) 'Int) 9))))
  (check-equal? name 'R-RawStore)
  (check-equal? (config-core after) (term unit))
  (check-equal? (config-heap after)
                (term ((0 (Rec ((f0 mut 9) (f1 imm 2)))
                           (declared ,rec-type))))))

(test-case "R-RawStore の型不一致 guard は書込み可能な欄で発火を止める"
  (define config
    (rec-config/declared `(RawStore ,(pointer '(f0) 'Bool) 9)))
  (check-equal? (step-count config) 0)
  (check-equal?
   (map first (raw-steps-g2/named
               (rec-config/declared
                `(RawStore ,(pointer '(f0) 'Int) 9))))
   '(R-RawStore)))

(test-case "Const の PtrVal への RawStore は発火しない（unsafe.md §2.3）"
  (check-equal?
   (step-count (rec-config/declared
                `(RawStore ,(pointer '(f0) 'Int 'Const) 9)))
   0))

;; unsafe.md §2.3。PtrOffset は fp を動かし、ptrmut を保って nul を Nullable にする。
;; fseg ::= label natural である。
(test-case "R-PtrOffset は末尾の添字を動かす（unsafe.md §2.3）"
  (for ([ptrmut (in-list '(Const Mut))])
    (match-define (list name after)
      (one-named (rec-config
                  `(PtrOffset ,(pointer '(f0 0) 'Int ptrmut) 2))))
    (check-equal? name 'R-PtrOffset)
    (check-equal? (config-core after)
                  (pointer '(f0 2) 'Int ptrmut 'Nullable))))

(test-case "末尾が label の fp では PtrOffset が発火しない（unsafe.md §2.3）"
  (check-equal?
   (step-count (rec-config `(PtrOffset ,(pointer '(f0) 'Int) 1)))
   0))

(test-case "負の添字になる PtrOffset は発火しない（unsafe.md §2.3）"
  (check-equal?
   (step-count
    (rec-config `(PtrOffset ,(pointer '(f0 0) 'Int) -1)))
   0))

;; AddressOf は root pointer だけを作る。自然数 segment を積むのは
;; R-EliminateRef だけだが、そこから渡るのは BorrowRef であり、AddressOf
;; が受ける BorrowMutRef ではない。Eliminate の可変借用版が入ったときは
;; この試験が落ち、R-PtrOffset の生成域・counter・仕様を回収する契機になる。
;; Const の PtrVal も同じ到達不能性を持つため、R-FromRawPtrConst は手組み
;; fixture で規則だけを検査している。
(test-case "root の借用から作った pointer では PtrOffset が発火しない（unsafe.md §2.3）"
  (match-define (list name after)
    (one-named
     (rec-config/declared
      (term (PtrOffset (AddressOf (BorrowMutRef 0 () (RVar 0))) 0)))))
  (check-equal? name 'R-AddressOf)
  (check-equal? (config-core after)
                `(PtrOffset ,(pointer '() rec-type) 0))
  (check-equal? (step-count after) 0))

;; 指す先が存在しない場合、RawLoad と RawStore は発火しない。
(test-case "存在しない欄への RawLoad は発火しない（unsafe.md §2.3）"
  (check-equal?
   (step-count (rec-config/declared `(RawLoad ,(pointer '(f9) 'Int))))
   0))

(test-case "存在しない欄への RawStore は発火しない（unsafe.md §2.3）"
  (check-equal?
   (step-count (rec-config/declared `(RawStore ,(pointer '(f9) 'Int) 9)))
   0))

;; unsafe.md §2.3。R-FromRawPtrConst と R-FromRawPtrMut は ptrmut で
;; 借用の種を分ける。
(test-case "FromRawPtr は ptrmut で規則が分かれる（unsafe.md §2.3）"
  (match-define (list name_c after_c)
    (one-named (rec-config/declared
                `(FromRawPtr ,(pointer '(f0) 'Int 'Const) (RVar 0)))))
  (check-equal? name_c 'R-FromRawPtrConst)
  (check-equal? (config-core after_c) (term (BorrowRef 0 (f0) (RVar 0))))
  (match-define (list name_m after_m)
    (one-named (rec-config/declared
                `(FromRawPtr ,(pointer '(f0) 'Int 'Mut) (RVar 0)))))
  (check-equal? name_m 'R-FromRawPtrMut)
  (check-equal? (config-core after_m) (term (BorrowMutRef 0 (f0) (RVar 0)))))

;; unsafe.md §2.3。Ω が Available でない place からは借用を作らない。
;; R-Borrow（machine.rkt:660）と同じ側条件を課す。pointer は静的な
;; borrow-check を通らずに手で組めるため、実行時にもここで閉じる。
(test-case "Moved の place からは FromRawPtr が発火しない（unsafe.md §2.3）"
  (check-equal?
   (step-count (moved-config
                `(FromRawPtr ,(pointer '(f0) 'Int 'Const) (RVar 0))))
   0)
  (check-equal?
   (step-count (moved-config
                `(FromRawPtr ,(pointer '(f0) 'Int 'Mut) (RVar 0))))
   0))

(test-case "FromRawPtr は pointee 型の不一致と owned 以外の provenance で発火しない"
  (check-equal?
   (call-with-trait-ledger
    pair-ledger
    (lambda ()
      (step-count
       (pair-config `(FromRawPtr ,(pointer '(1) 'Int 'Const) (RVar 0))))))
   0)
  (check-equal?
   (step-count (rec-config/declared
                `(FromRawPtr ,(pointer '(f0) 'Int 'Const 'NonNull
                                       '(Prov foreign)) (RVar 0))))
   0))

(test-case "Moved の place への RawLoad は発火しない（unsafe.md §2.3）"
  (check-equal?
   (step-count (moved-config `(RawLoad ,(pointer '(f0) 'Int))))
   0))

(test-case "Moved の place への RawStore は発火しない（unsafe.md §2.3）"
  (check-equal?
   (step-count (moved-config `(RawStore ,(pointer '(f0) 'Int) 9)))
   0))

;; unsafe.md §4.2。R-UnsafeExit は内側が値になったら枠を外す。
(test-case "R-UnsafeExit は枠を外す（unsafe.md §4.2）"
  (match-define (list name after) (one-named (rec-config (term (Unsafe 7)))))
  (check-equal? name 'R-UnsafeExit)
  (check-equal? (config-core after) (term 7)))

;; unsafe.md §4.2。Unsafe の内側の Perform が伝播する。
;; F の枠を置く根拠の回帰である。
(test-case "Unsafe の内側の Perform が伝播する（unsafe.md §4.2）"
  (match-define (list name after)
    (one-named
     (rec-config
      (term (Handle (Return b Int) (k -> k)
                    (Unsafe (Perform (Return b Int) 3)))))))
  (check-equal? name 'R-HandleReturn)
  (check-equal? (config-core after) (term 3)))

;; unsafe.md §4.2。R-LetOwned は G 文脈内でも Unsafe の枠を保つ。
(test-case "Unsafe の枠は G を越える（unsafe.md §4.2）"
  (match-define (list name after)
    (one-named
     (term (cfg (Scope ()
                       (Unsafe (Let (r (Owned Res))
                                    (resource 9)
                                    (Move r))))
                () () () ()))))
  (check-equal? name 'R-LetOwned)
  (check-equal? (config-core after)
                (term (Scope (0) (Unsafe (Move 0))))))
