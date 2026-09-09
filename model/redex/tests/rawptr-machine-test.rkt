#lang racket

(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../machine.rkt"
         "../gen.rkt")

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

;; unsafe.md §2.3。Ω が Available でない場合の負例を取るための config。
(define (moved-config core)
  (term (cfg ,core ((0 (Rec ((f0 mut 1) (f1 imm 2)))))
             ((0 Moved)) () ())))

;; unsafe.md §2.3。R-AddressOf は可変借用から PtrVal を作る。
;; PtrVal は ptrmut を実行時にも運ぶ。
(test-case "R-AddressOf は Mut の PtrVal を作る（unsafe.md §2.3）"
  (match-define (list name after)
    (one-named (rec-config (term (AddressOf (BorrowMutRef 0 () (RVar 0)))))))
  (check-equal? name 'R-AddressOf)
  (check-equal? (config-core after) (term (PtrVal 0 () Mut (Prov owned)))))

;; unsafe.md §2.3。R-RawLoad は Const と Mut の両方で発火する。
(test-case "R-RawLoad は H の該当欄を読む（unsafe.md §2.3）"
  (for ([ptrmut (in-list '(Const Mut))])
    (match-define (list name after)
      (one-named (rec-config `(RawLoad (PtrVal 0 (f0) ,ptrmut (Prov owned))))))
    (check-equal? name 'R-RawLoad)
    (check-equal? (config-core after) (term 1))))

;; unsafe.md §2.3。R-RawStore は Mut の PtrVal に限る。
(test-case "R-RawStore は H の該当欄を書く（unsafe.md §2.3）"
  (match-define (list name after)
    (one-named (rec-config (term (RawStore (PtrVal 0 (f0) Mut (Prov owned)) 9)))))
  (check-equal? name 'R-RawStore)
  (check-equal? (config-core after) (term unit))
  (check-equal? (config-heap after)
                (term ((0 (Rec ((f0 mut 9) (f1 imm 2))))))))

(test-case "Const の PtrVal への RawStore は発火しない（unsafe.md §2.3）"
  (check-equal?
   (step-count (rec-config (term (RawStore (PtrVal 0 (f0) Const (Prov owned)) 9))))
   0))

;; unsafe.md §2.3。PtrOffset は fp の末尾の添字を動かし ptrmut を保つ。
;; fseg ::= label natural である。
(test-case "R-PtrOffset は末尾の添字を動かす（unsafe.md §2.3）"
  (for ([ptrmut (in-list '(Const Mut))])
    (match-define (list name after)
      (one-named (rec-config
                  `(PtrOffset (PtrVal 0 (f0 0) ,ptrmut (Prov owned)) 2))))
    (check-equal? name 'R-PtrOffset)
    (check-equal? (config-core after)
                  `(PtrVal 0 (f0 2) ,ptrmut (Prov owned)))))

(test-case "末尾が label の fp では PtrOffset が発火しない（unsafe.md §2.3）"
  (check-equal?
   (step-count (rec-config (term (PtrOffset (PtrVal 0 (f0) Mut (Prov owned)) 1))))
   0))

;; 指す先が存在しない場合、RawLoad と RawStore は発火しない。
(test-case "存在しない欄への RawLoad は発火しない（unsafe.md §2.3）"
  (check-equal?
   (step-count (rec-config (term (RawLoad (PtrVal 0 (f9) Mut (Prov owned))))))
   0))

(test-case "存在しない欄への RawStore は発火しない（unsafe.md §2.3）"
  (check-equal?
   (step-count (rec-config (term (RawStore (PtrVal 0 (f9) Mut (Prov owned)) 9))))
   0))

;; unsafe.md §2.3。R-FromRawPtrConst と R-FromRawPtrMut は ptrmut で
;; 借用の種を分ける。
(test-case "FromRawPtr は ptrmut で規則が分かれる（unsafe.md §2.3）"
  (match-define (list name_c after_c)
    (one-named (rec-config
                (term (FromRawPtr (PtrVal 0 (f0) Const (Prov owned)) (RVar 0))))))
  (check-equal? name_c 'R-FromRawPtrConst)
  (check-equal? (config-core after_c) (term (BorrowRef 0 (f0) (RVar 0))))
  (match-define (list name_m after_m)
    (one-named (rec-config
                (term (FromRawPtr (PtrVal 0 (f0) Mut (Prov owned)) (RVar 0))))))
  (check-equal? name_m 'R-FromRawPtrMut)
  (check-equal? (config-core after_m) (term (BorrowMutRef 0 (f0) (RVar 0)))))

;; unsafe.md §2.3。Ω が Available でない place からは借用を作らない。
;; R-Borrow（machine.rkt:660）と同じ側条件を課す。pointer は静的な
;; borrow-check を通らずに手で組めるため、実行時にもここで閉じる。
(test-case "Moved の place からは FromRawPtr が発火しない（unsafe.md §2.3）"
  (check-equal?
   (step-count (moved-config
                (term (FromRawPtr (PtrVal 0 (f0) Const (Prov owned)) (RVar 0)))))
   0)
  (check-equal?
   (step-count (moved-config
                (term (FromRawPtr (PtrVal 0 (f0) Mut (Prov owned)) (RVar 0)))))
   0))

;; unsafe.md §4.2。R-UnsafeExit は内側が値になったら枠を外す。
(test-case "R-UnsafeExit は枠を外す（unsafe.md §4.2）"
  (match-define (list name after) (one-named (rec-config (term (Unsafe 7)))))
  (check-equal? name 'R-UnsafeExit)
  (check-equal? (config-core after) (term 7)))

;; unsafe.md §4.2。Unsafe の内側の Perform が伝播する。
;; F と G の枠を置く根拠の回帰である。
(test-case "Unsafe の内側の Perform が伝播する（unsafe.md §4.2）"
  (check-true
   (positive?
    (step-count
     (rec-config
      (term (Handle (Return b Int) (k -> k)
                    (Unsafe (Perform (Return b Int) 3)))))))))
