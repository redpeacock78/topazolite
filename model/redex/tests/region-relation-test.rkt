#lang racket

(require rackunit
         racket/set
         "../compat.rkt"
         "../region.rkt"
         "../region-param.rkt")

;; spec §6.1 の 3 規則と §6.2 の既定の不変性。
;; 具体的な region の番号は大域の採番に依るため、literal を書かず
;; region-at と region->rho から取る。

(define skeleton '(Scope () (Scope () 0)))
(define ir (build-region-ir skeleton))
(define outer (region->rho ir (region-at ir '())))
(define inner (region->rho ir (region-at ir '(0 0))))
(check-not-equal? outer inner)

;; 表を作る元の項。外側の RegionLam の本体に outer が現れ、
;; inner は内側の RegionLam の中にだけ現れる。
(define binder-core
  `(RegionLam (a)
     (Scope ()
       (Let (x let (Borrowed Int ,outer)) (Borrow y)
            (RegionLam (b)
              (Let (z let (Borrowed Int ,inner)) (Borrow y) z))))))

(define relation (make-region-relation ir binder-core))

;; region-slot-table の BorrowAt、BorrowRef、RegionApp の欄も走査する。
;; 各 binder は別の形だけを本体に持たせ、1 つの欄の誤りを別の出現で
;; 覆い隠さない。
(define slot-core
  `(Scope ()
     (RegionLam (slot-at)
       (BorrowAt ,outer (Own 1 ()) y))
     (RegionLam (slot-ref)
       (UVal (BorrowRef 1 () ,outer)))
     (RegionLam (slot-app)
       (RegionApp (Borrow y) (,outer)))))
(define slot-relation (make-region-relation ir slot-core))
(test-case
 "BorrowAt BorrowRef RegionApp の region 欄を走査する"
 (check-true (slot-relation '(RParam slot-at) outer))
 (check-true (slot-relation '(RParam slot-ref) outer))
 (check-true (slot-relation '(RParam slot-app) outer)))

;; α 付け替え前の重複を黙って後勝ちにしない。未付け替えの IR を
;; fail-closed で拒むことで、別 binder の表が混ざることを防ぐ。
(test-case
 "重複した RegionLam の束縛名は拒む"
 (check-exn exn:fail?
            (lambda ()
              (make-region-relation ir
                                    '(RegionLam (dup)
                                       (RegionLam (dup) 0))))))

;; 規則 1。同じ (RParam rp) は真である。
(test-case
 "規則 1 反射律"
 (check-true (relation '(RParam a) '(RParam a)))
 (check-true (relation '(RParam b) '(RParam b))))

;; 規則 3 のうち、別の binder に由来する 2 つの (RParam rp) は偽である。
;; 付け替え後の名前で判定するため、名前が違えば束縛元も違う。
(test-case
 "別の binder の rp は偽である"
 (check-false (relation '(RParam a) '(RParam b)))
 (check-false (relation '(RParam b) '(RParam a))))

;; 規則 2。左辺が rp で右辺が具体的な region なら、本体に現れる region に限り真。
(test-case
 "規則 2 本体に現れる region に限り真である"
 (check-true (relation '(RParam a) outer))
 ;; inner は内側の RegionLam の中にだけ現れるため、a の表には入らない。
 (check-false (relation '(RParam a) inner))
 ;; 内側の binder の表には inner が入る。
 (check-true (relation '(RParam b) inner))
 (check-false (relation '(RParam b) outer)))

;; 規則 3。左辺が具体的な region で右辺が rp なら偽である。
(test-case
 "規則 3 具体から rp へは偽である"
 (check-false (relation outer '(RParam a)))
 (check-false (relation inner '(RParam b))))

;; 表に無い binder の名前は空集合として扱う。fail-closed である。
(test-case
 "未知の binder は空集合として扱う"
 (check-false (relation '(RParam unknown) outer)))

;; どちらも rp でなければ region-outlives? へ渡す。
(test-case
 "具体どうしは region-outlives? である"
 (check-true (relation outer outer))
 (check-true (relation outer inner))
 (check-false (relation inner outer)))

;; 解決前の寿命変数は ir に属さないため、equal? で判定する。
(test-case
 "RVar は equal? で判定する"
 (check-true (relation '(RVar 0) '(RVar 0)))
 (check-false (relation '(RVar 0) '(RVar 1)))
 (check-false (relation '(RVar 0) outer)))

;; §6.2。既定のままの compat? は今日と同じ equal? 判定である。
(test-case
 "compat? の既定は equal? である"
 (check-true (compat? `(Borrowed Int ,outer) `(Borrowed Int ,outer) '()))
 (check-false (compat? `(Borrowed Int ,inner) `(Borrowed Int ,outer) '()))
 (check-true (compat? `(BorrowedMut Int ,outer) `(BorrowedMut Int ,outer) '()))
 (check-false (compat? `(BorrowedMut Int ,inner) `(BorrowedMut Int ,outer) '())))

;; 段 B は関係を Borrowed の region 欄で消費する。
;; 束縛された (RParam r) は、その RegionLam の本体に現れる具体的な region を
;; 含む。表に無い region は含まない。
(test-case
 "関係を渡すと Borrowed の region 欄が共変になる"
 (check-true (compat? `(Borrowed Int (RParam a)) `(Borrowed Int ,outer)
                      '() relation))
 (check-false (compat? `(Borrowed Int (RParam a)) `(Borrowed Int ,inner)
                       '() relation))
 (check-true (compat? `(Borrowed Int ,outer) `(Borrowed Int ,outer)
                      '() relation))
 (check-true (compat? `(Borrowed Int ,outer) `(Borrowed Int ,inner)
                      '() relation))
 (check-false (compat? `(Borrowed Int ,inner) `(Borrowed Int ,outer)
                       '() relation))
 (check-true (compat? `(BorrowedMut Int ,outer) `(BorrowedMut Int ,outer)
                      '() relation)))

;; 関係は再帰の全経路へ届く。呼ばれた組を記録する spy を渡し、
;; 各構成子の下にある共有借用の region 欄まで届くことを見る。
;; spy の判定は equal? と同じであり、記録だけを足す。
(define (spy-relation calls)
  (lambda (left right)
    (set-box! calls (cons (list left right) (unbox calls)))
    (equal? left right)))

(test-case
 "関係は NFn と構築子の再帰へ届く"
 (for ([shape (in-list (list `(NFn (Int) (Borrowed Int ,outer) () ())
                             `(NFn ((Borrowed Int ,outer)) Int () ())
                             `(Record ((f (Borrowed Int ,outer) imm)))
                             `(Union (Borrowed Int ,outer) Int)
                             `(Untrusted (Borrowed Int ,outer))
                             `(Refined (Borrowed Int ,outer)
                                       (Implements Int Tn))))])
   (define calls (box '()))
   (check-true (compat? shape shape '() (spy-relation calls)))
   (check-false (null? (unbox calls)))))

;; 可変借用の region 欄は関係を消費しない。equal? で判定し続ける。
(test-case
 "可変借用の region 欄は関係を消費しない"
 (for ([shape (in-list (list `(BorrowedMut Int ,outer)
                             `(Record ((f (BorrowedMut Int ,outer) mut)))))])
   (define calls (box '()))
   (check-true (compat? shape shape '() (spy-relation calls)))
   (check-true (null? (unbox calls)))))

;; parameter の既定は equal? である。
(test-case
 "current-region-relation の既定は equal? である"
 (check-eq? (current-region-relation) equal?))
