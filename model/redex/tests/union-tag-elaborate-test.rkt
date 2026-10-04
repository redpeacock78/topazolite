#lang racket

(require rackunit
         racket/match
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../type-equiv.rkt"
         "../typing.rkt")

;; P2m2b spec の回帰。tag mode の下で elaborate し、生成した Core を
;; 同じ mode の Core typing に通して、型と行が elaborate と一致することを確かめる。
(define-syntax-rule (tagged body ...)
  (parameterize ([current-union-tag-mode #t]) body ...))

(define (elab/tag source) (tagged (elab source)))

(define (accepted source)
  (match (elab/tag source)
    [(list core type row callables)
     (check-equal? (tagged (core-type-of core '() callables))
                   (list type row)
                   (format "source: ~s" source))
     (list (erase-core core) type row)]
    [`(err ,d) (fail-check (format "elaborate が拒否した: ~s" d))]))

(define (rejected-code source)
  (match (elab/tag source)
    [`(err ,d) (diagnostic-id d)]
    [other (fail-check (format "elaborate が受理した: ~s" other))]))

(define (code key) (diagnostic-code-of 'elaborate key))

(define (count-nodes head tree)
  (cond [(and (pair? tree) (eq? (car tree) head))
         (add1 (apply + (map (lambda (t) (count-nodes head t)) (cdr tree))))]
        [(pair? tree) (apply + (map (lambda (t) (count-nodes head t)) tree))]
        [else 0]))

(define IS '(Union Int String))
(define ISB '(Union Int (Union String Bool)))

(test-case "注釈付き Let は非 Union の値を Union へ inject する"
  (match-define (list core type _) (accepted `(Let (x const ,IS) 1 x)))
  (check-equal? type (normalize-type IS))
  (check-equal? (count-nodes 'UnionInject core) 1))

(test-case "tag を持つ Union を広い Union へ渡すのは恒等である"
  (match-define (list core _ _)
    (accepted `(Let (x const ,IS) 1 (Let (y const ,ISB) x y))))
  (check-equal? (count-nodes 'UnionEliminate core) 0))

(test-case "Union を非 Union の expected へ分解して渡す"
  ;; Never はどの expected にも合い、tag-compat? は Union 全体を非 Union へ渡さない。
  (match-define (list core _ _)
    (accepted `(Let (x const (Union Int Never))
                 1
                 (Let (y const Int) x y))))
  (check-equal? (count-nodes 'UnionEliminate core) 1))

(test-case "完全一致の成分を優先し、無ければ一意な tag-compat? の成分を選ぶ"
  (void (accepted
         `(Let (x const (Union (Refined Int (Prop ValidPort)) Int)) 1 x)))
  (match-define (list injected _ _)
    (accepted
     '(Let (x const (Union (Record ((a Int imm))) Bool))
           (Rec ((a imm 1) (b imm 2)))
           x)))
  (check-equal? (count-nodes 'UnionInject injected) 1)
  (check-equal?
   (rejected-code
    '(Let (x const (Union (Record ((a Int imm))) (Record ((b Int imm)))))
          (Rec ((a imm 1) (b imm 2)))
          x))
   (code 'ambiguous-union-member)))

(test-case "Record の expected へ残余の異なる成分の Union を渡す"
  (void
   (accepted
    '(Let (u const (Union (Record ((a Int imm) (b Bool imm)))
                          (Record ((a Int imm) (c String imm)))))
          (Rec ((a imm 1) (b imm (Construct true (Types)))))
          (Let (r let (Record ((a Int imm)))) u r)))))

(test-case "共通の残余が上界で合流できない Union は type-mismatch で拒否する"
  (check-equal?
   (rejected-code
    '(Let (u const (Union (Record ((a Int imm) (b Int imm)))
                          (Record ((a Int imm) (b String imm)))))
          (Rec ((a imm 1) (b imm 2)))
          (Let (r let (Record ((a Int imm)))) u r)))
   (code 'type-mismatch)))

(test-case "Apply の引数と Rec の欄でも inject する"
  (match-define (list core _ _)
    (accepted `(Apply (Fn ((v ,IS)) ,IS () v) 1)))
  (check-equal? (count-nodes 'UnionInject core) 1)
  (match-define (list core2 _ _)
    (accepted `(Let (r const (Record ((f ,IS imm)))) (Rec ((f imm 1))) r)))
  (check-equal? (count-nodes 'UnionInject core2) 1))

(test-case "明示型引数の constructor の欄でも inject する"
  ;; Apply の引数は check を通るので、check の Construct (Types …) 節に届く。
  ;; 注釈付き Let の bound は needs-expected-type? が #f なので synth へ進み、
  ;; この節を通らない。
  ;; 内側の欄の 1 と、外側の Option から Union への 2 か所で inject する。
  (match-define (list core type _)
    (accepted `(Apply (Fn ((o (Union (Option ,IS) Bool))) Int () 0)
                      (Construct some (Types ,IS) 1))))
  (check-equal? type 'Int)
  (check-equal? (count-nodes 'UnionInject core) 2))

(test-case "生成した binder は入力の symbol と衝突しない"
  (match-define (list core _ _)
    (accepted `(Let (union0 const (Union Int Never))
                 1
                 (Let (y const Int) union0 y))))
  (check-equal? (count-nodes 'UnionEliminate core) 1))

(test-case "mode off では変換を置かない"
  (match (elab `(Let (x const ,IS) 1 x))
    [(list core _ _ _)
     (check-equal? (count-nodes 'UnionInject (erase-core core)) 0)]
    [other (fail-check (format "mode off で拒否した: ~s" other))]))
