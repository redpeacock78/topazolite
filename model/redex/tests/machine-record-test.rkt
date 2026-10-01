#lang racket
(require rackunit
         redex/reduction-semantics
         "../lang.rkt"
         "../machine.rkt"
         "../typing.rkt")

(define fuel 40)
(define acquire (term (PrimVal (Reserved o-acquire) acquire)))

; heap が空の項用: (cfg result () () ()) を unwrap する
(define (run-g2-core core)
  (match (run-g2 (inject-g2 core) fuel)
    [`(cfg ,result () () () ()) result]
    [result (error 'run-g2-core "unexpected: ~e" result)]))

; 1 手も進めなければ stuck とみなす
(define (stuck-g2? core)
  (null? (apply-reduction-relation -->g2 (inject-g2 core))))

; (a) R-Proj hit: 射影が field 値へ簡約
(check-equal? (run-g2-core (term (Proj (Rec ((a imm 1) (b imm unit))) a))) (term 1))

; (b) R-Proj missing-label: 不在ラベルの射影は stuck（proj-lookup が #f、side-condition で不発火）
(check-true (stuck-g2? (term (Proj (Rec ((a imm 1))) z))))

; (c) R-LetB const: 非 Owned の binding は代入
(check-equal? (run-g2-core (term (Let (x const Int) 1 (Proj (Rec ((a imm x))) a)))) (term 1))

; (d) R-LetB let: bmode は実行時に消え const と同じく代入される
(check-equal?
 (run-g2-core
  (term (Let (x let (Record ((a Int imm)))) (Rec ((a imm 1))) (Proj x a))))
 (term 1))

; (e) R-LetOwnedB: Owned は bmode 付き Let でも move される（G1 R-LetOwned と同じ heap 遷移）
(check-equal?
 (run-g2 (inject-g2 (term (Let (r const (Owned Res)) (Apply ,acquire 0) (Move r)))) fuel)
 (term (cfg (resource 0) ((0 (resource 0))) ((0 Moved)) () ())))

; (f) Rec のフィールドは記述順に E 文脈で簡約される（congruence）
(check-equal?
 (run-g2-core (term (Rec ((a imm (Proj (Rec ((x imm 1))) x)) (b imm 2)))))
 (term (Rec ((a imm 1) (b imm 2)))))

; (g) G1 項は -->g2 でも簡約される（後方互換）
(check-equal? (run-g2-core (term (Apply (PrimVal (Reserved o-add) add) 7 3))) (term 10))

; (h) R-Beta: 引数 Rec を substitute*/g2 で body の Proj へ代入
(check-equal?
 (run-g2-core (term (Apply (Lam User f-id (x) (Proj x a)) (Rec ((a imm 1) (b imm 2))))))
 (term 1))

; (i) R-RecurUnfold: RecurVal の body に Rec。substitute*/g2 が f と x を代入
(check-equal?
 (run-g2-core (term (Apply (RecurVal r-id f (x) (Rec ((a imm x)))) 7)))
 (term (Rec ((a imm 7)))))

; (j) R-Eliminate: 非先頭 constructor (cons) の枝が Rec を返す
;     （select-branch/g2 の第 2 節の自己再帰と第 1 節の substitute*/g2 を同時に踏む）
(check-equal?
 (run-g2-core
  (term (Eliminate (Construct (List Int) cons 3 (Construct (List Int) nil))
                   ((nil () -> (Rec ((a imm 0))))
                    (cons (h t) -> (Rec ((a imm h))))))))
 (term (Rec ((a imm 3)))))

; (k) 重複ラベルの Rec の射影は例外でなく stuck（unique-labels? side-condition で不発火）
(check-true (stuck-g2? (term (Proj (Rec ((a imm 1) (a imm 2))) a))))

; (l) Rec の field 内の Perform が F 文脈を通って handler に捕捉される
; （structural-row.md §5.1 で Rec を F へ）
(check-equal?
 (run-g2 (inject-g2
   (term (Handle (Return boundary Int)
                 (answer -> answer)
                 (Rec ((a imm (Perform (Return boundary Int) 42))))))) fuel)
 (term (cfg 42 () () () ())))

; R-ProjOpt は欄があれば some、無ければ none を作る。
(check-equal?
 (run-g2-core
  (term (ProjOpt Int
                 (Let (r const (Record ((a Int imm) (b Int imm opt))))
                      (Rec ((a imm 1) (b imm 2)))
                      r)
                 b)))
 (term (Construct (Option Int) some 2)))
(check-equal?
 (run-g2-core
  (term (ProjOpt Int
                 (Let (r const (Record ((a Int imm) (b Int imm opt))))
                      (Rec ((a imm 1)))
                      r)
                 b)))
 (term (Construct (Option Int) none)))
; Absent は欄の不在を値に保ち、束縛後も none へ射影される。
(check-equal?
 (run-g2-core
  '(Let (r const (Record ((a Int imm) (b Int imm opt))))
     (Rec ((a imm 1) (b imm (Absent Int))))
     (ProjOpt Int r b)))
 '(Construct (Option Int) none))
(check-equal?
 (run-g2-core
  '(ProjOpt Int
     (Rec ((a imm 1) (b imm (Absent Int))))
     b))
 '(Construct (Option Int) none))
(define absent-projopt-after-let
  (first
   (raw-steps-g2
    (inject-g2
     '(Let (r const (Record ((a Int imm) (o Int imm opt))))
        (Rec ((a imm 1) (o imm (Absent Int))))
        (ProjOpt Int r o))))))
(check-equal?
 absent-projopt-after-let
 '(cfg (Scope () (ProjOpt Int (Rec ((a imm 1) (o imm (Absent Int)))) o))
       () () () ()))
(check-equal?
 (core-type-of '(Scope () (ProjOpt Int (Rec ((a imm 1) (o imm (Absent Int)))) o))
               '() '())
 '((Option Int) ()))
; 型が optional でも値に欄が残れば some を返す。
(check-equal?
 (run-g2-core
  (term (Let (s const (Record ((a Int imm) (b Int imm))))
             (Rec ((a imm 1) (b imm 2)))
             (ProjOpt Int
                      (Let (r const (Record ((a Int imm) (b Int imm opt))))
                           s
                           r)
                      b))))
 (term (Construct (Option Int) some 2)))

;; Absent 欄を持つ literal は置換後も optional の欄として射影できる。
(check-equal?
 (run-g2-core
  (term (Proj
         (Let (x const (Record ((a Int imm) (b Int imm opt))))
              (Rec ((a imm 1) (b imm (Absent Int))))
              x)
         a)))
 (term 1))

;; by-value の再代入は元の場所を書き換えない。
(check-equal?
 (run-g2 (inject-g2
          (term (Let (s const (Record ((a Int imm))))
                     (Rec ((a imm 1)))
                 (Let (x mut (Record ((a Int imm opt))))
                      s
                  (Let (y const (Record ((a Int imm opt))))
                       (Rec ((a imm 2)))
                   (Let (ignored const Unit)
                        (Reassign x y)
                        (Proj s a)))))))
         fuel)
 (term (cfg 1 ((0 (Rec ((a imm 2))))) ((0 Dropped)) () ((fin 0)))))

; Absent の Owned 欄は drop でも観測でも token を要求しない。
(check-equal?
 (run-g2 (inject-g2
          '(Drop (Rec ((owned imm (Absent (Owned Res)))))))
         fuel)
 '(cfg unit () () () ()))
(check-equal?
 (run-g2 (inject-g2
          '(Yield (Rec ((owned imm (Absent (Owned Res))))) unit))
         fuel)
 '(cfg unit () () () ((obs (Rec ((owned imm (Absent (Owned Res)))))))))
