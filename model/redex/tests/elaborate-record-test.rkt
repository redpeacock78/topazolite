#lang racket
(require rackunit racket/match "../elaborate.rkt")

; elab は 1 引数で、成功時に (list core type row callables) を返す（elaborate.rkt:294、
; 687-690）。Δ0／Γ0／Π0 は elab 内部で使われ、外部 API は 1 引数である。
; 既存 elaborate-test.rkt の (match-define (list core _ _ _) (elab '...)) 規約に合わせる。
(define (elab-core term) (match (elab term) [(list core _ _ _) core]))
(define (elab-type term) (match (elab term) [(list _ type _ _) type]))
(define (elab-row  term) (match (elab term) [(list _ _ row _) row]))
; 失敗時は (err reason)。elaborate-test.rkt の elaboration-error? に倣う。
(define (elab-error? term) (match (elab term) [`(err ,_) #t] [_ #f]))

; record リテラル: (Rec ((label m e) ...)) → (Rec ((label m c) ...))
(check-equal? (elab-core '(Rec ((a imm 1) (b mut 2))))
              '(Rec ((a imm 1) (b mut 2))))
; Rec の型は (Record ((label τ m) ...)) 順、effect row は field effect の和
(check-equal? (elab-type '(Rec ((a imm 1) (b mut 2))))
              '(Record ((a Int imm) (b Int mut))))
(check-equal? (elab-row '(Rec ((a imm (Suspend 1)) (b imm 2)))) '(Suspend))
; 射影: (Proj e label) → (Proj c label)。effect row は scrutinee の effect
(check-equal? (elab-core '(Proj (Rec ((a imm 1))) a))
              '(Proj (Rec ((a imm 1))) a))
(check-equal? (elab-type '(Proj (Rec ((a imm 1) (b mut unit))) b)) 'Unit)
(check-equal? (elab-row  '(Proj (Rec ((a imm (Suspend 1)))) a)) '(Suspend))
; Rec の Owned field は拒否（(Apply acquire N) は Owned<Res> に synth される。record 値の field に Owned を許さない）
(check-true (elab-error? '(Rec ((a imm (Apply acquire 1))))))
; ラベル重複も拒否（structural-row.md §2.2 field-row-unique?）
(check-true (elab-error? '(Rec ((a imm (Suspend 1)) (a mut 2)))))
; 注釈なし G1 Let は旧形のまま（新形へ正規化しない。structural-row.md §4／回帰維持）
(check-equal? (elab-core '(Let x 1 x)) '(Let (x Int) 1 x))
; 注釈あり let → binding mode 付き Let（注釈型は resolve-annotation で (label τ m) 順に解決）
(check-equal? (elab-core '(Let (x let (Record ((a Int imm)))) (Rec ((a imm 1))) x))
              '(Let (x let (Record ((a Int imm)))) (Rec ((a imm 1))) x))
; bmode Let の effect row は bound と body の effect の和
(check-equal? (elab-row '(Let (x const Int) (Suspend 1) x)) '(Suspend))
; 重複ラベルの record 型注釈は ill-formed（structural-row.md §2.2）
(check-true (elab-error? '(Let (x let (Record ((a Int imm) (a Bool mut)))) (Rec ((a imm 1))) x)))
; const は残余空を要求。注釈 {a} に bound {a,b} だと残余 {b} が非空で拒否（structural-row.md §3.2）
(check-true (elab-error? '(Let (x const (Record ((a Int imm)))) (Rec ((a imm 1) (b imm 2))) x)))
; let は残余 {b} を x の型へ保持し、body で Proj x b が Int を返す（structural-row.md §3.2）
(check-equal? (elab-type '(Let (x let (Record ((a Int imm)))) (Rec ((a imm 1) (b imm 2))) (Proj x b)))
              'Int)
