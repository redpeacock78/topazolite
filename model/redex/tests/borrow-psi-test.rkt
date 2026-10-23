#lang racket

(require rackunit racket/set
         "../region.rkt"
         "../borrow.rkt")

(define ρ1 (region 100))
(define ρ2 (region 101))

;; psi-join は permission だけを合併し、flow は呼び出し側へ委ねる。
(define flow-a (flow-state (hash 'x (flow-entry 'Int 'Int #f)) (hash)))
(define flow-b (flow-state (hash 'y (flow-entry 'String 'String #f)) (hash)))
(define Ψa (psi (set '(x () 100)) (set) (set) flow-a))
(define Ψb (psi (set '(y () 101)) (set '(z () 100)) (set) flow-b))

(check-equal? (psi-join Ψa Ψb)
              (psi (set '(x () 100) '(y () 101)) (set '(z () 100)) (set) flow-a))

;; permission 欄だけは可換かつ冪等である。
(check-equal? (psi-shared (psi-join Ψa Ψb))
              (psi-shared (psi-join Ψb Ψa)))
(check-equal? (psi-mut (psi-join Ψa Ψb))
              (psi-mut (psi-join Ψb Ψa)))
(check-equal? (psi-join Ψa Ψa) Ψa)

;; Ψ から項目を落とす操作はもう無い。合流は合併のままである。
(let ()
  (define a1 '(RVar 0))
  (define a2 '(RVar 1))
  (define base-flow (flow-state (hash 'x (flow-entry 'Int 'Int #f)) (hash)))
  (define Ψ1 (psi-add-shared (struct-copy psi (empty-psi) [flow base-flow]) 'x '() a1))
  (define Ψ2 (psi-add-mut (struct-copy psi (empty-psi) [flow flow-b]) 'y '() a2))
  (check-equal? (psi-shared (psi-join Ψ1 Ψ2))
                (set (list 'x '() a1)))
  (check-equal? (psi-mut (psi-join Ψ1 Ψ2))
                (set (list 'y '() a2)))
  (check-equal? (psi-flow (psi-join Ψ1 Ψ2)) base-flow))

;; mut に (x ρ2) があるときは、退避と子の共有借用の両方を行う。
(check-equal? (psi-suspend (psi (set) (set (list 'x '() ρ2)) (set) flow-a)
                           'x '() ρ2 ρ1 '(Reborrow x))
              (psi (set (list 'x '() ρ1))
                   (set)
                   (set (list 'x '() ρ2 ρ1 '(Reborrow x) #f #f))
                   flow-a))

;; mut に無いときは共有借用だけを張り、退場時に mut を新規作成しない。
(check-equal? (psi-suspend (empty-psi) 'x '() ρ2 ρ1 '(Reborrow x))
              (psi (set (list 'x '() ρ1)) (set) (set)
                   (flow-state (hash) (hash))))

;; 射影した再借用は祖先 path の mut capability を親として停止する。
(let* ([parent (list 'x '() ρ2)]
       [Ψ (psi (set) (set parent) (set) (flow-state (hash) (hash)))]
       [point '(3 1)]
       [suspended (psi-suspend Ψ 'x '(a) ρ2 ρ1 '(Reborrow field) point)])
  (check-equal? (psi-mut suspended) (set parent))
  (check-equal? (psi-suspended suspended)
                (set (list 'x '(a) ρ2 ρ1 '(Reborrow field) point #f))))
