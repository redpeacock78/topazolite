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

(define (if-source then-branch else-branch)
  `(Eliminate (Construct true (Types))
              ((true () -> ,then-branch) (false () -> ,else-branch))))

(define (all-never-if-source)
  '(Fn ((s (NFn () Never (Suspend) ()))
        (p (NFn () Never (Partial) ())))
       Int (Suspend Partial)
       (Let x
            (Eliminate (Construct true (Types))
                       ((true () -> (Apply s)) (false () -> (Apply p))))
            (Let (n const Never) x 0))))

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

(test-case "Record への分解では Never 成分を合流から除く"
  (match-define (list core type _)
    (accepted
     '(Let (u const (Union (Record ((a Int imm) (b Int imm))) Never))
           (Rec ((a imm 1) (b imm 2)))
           (Let (r let (Record ((a Int imm)))) u r))))
  (check-equal? type '(Record ((a Int imm) (b Int imm))))
  (check-equal? (count-nodes 'UnionEliminate core) 1))

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

(test-case "tag mode の Reassign は非 Union の右辺を slot の Union へ inject する"
  (match-define (list core _ _)
    (accepted `(Let (x mut ,IS) 1 (Reassign x "s"))))
  (check-equal? (count-nodes 'UnionInject core) 2))

(test-case "Reassign は Union の右辺を分解しない"
  (check-equal?
   (rejected-code
    `(Let (x mut Int) 1
          (Let (y const ,IS) 1 (Reassign x y))))
   (code 'reassign-type-mismatch)))

(test-case "Reassign は tag-narrowing? で合う Union の右辺をそのまま渡す"
  (match-define (list core _ _)
    (accepted `(Let (x mut ,ISB) 1
                 (Let (y const ,IS) 1 (Reassign x y)))))
  (check-equal? (count-nodes 'UnionEliminate core) 0))

(test-case "Reassign の Never の右辺は inject しない"
  ;; Return は右辺で synth されて Never になる。§3.2 へ渡すと
  ;; 全ての成分が候補になり ambiguous-union-member になる。
  (match-define (list core _ _)
    (accepted `(Fn () Unit (Mutation)
                 (Let (x mut ,IS) 1 (Reassign x (Return unit))))))
  (check-equal? (count-nodes 'UnionInject core) 1))

(test-case "mode off の Reassign は従来どおり type-equiv? を使う"
  (match (elab `(Let (x mut ,IS) 1 (Reassign x "s")))
    [`(err ,d) (check-equal? (diagnostic-id d)
                             (code 'reassign-type-mismatch))]
    [other (fail-check (format "mode off で受理した: ~s" other))]))

(test-case "Reassign で slot の Union に合わない値は reassign-type-mismatch"
  (check-equal?
   (rejected-code
    `(Let (x mut ,IS) 1
          (Reassign x (Construct true (Types)))))
   (code 'reassign-type-mismatch)))

(test-case "mode off では変換を置かない"
  (match (elab `(Let (x const ,IS) 1 x))
    [(list core _ _ _)
     (check-equal? (count-nodes 'UnionInject (erase-core core)) 0)]
    [other (fail-check (format "mode off で拒否した: ~s" other))]))

(test-case "注釈の無い if は枝の型の Union を返す"
  (match-define (list core type _) (accepted `(Let x ,(if-source 1 "s") x)))
  (check-equal? type (normalize-type IS))
  (check-equal? (count-nodes 'UnionInject core) 2))

(test-case "同値な枝の if は inject を置かない"
  (match-define (list core type _) (accepted `(Let x ,(if-source 1 2) x)))
  (check-equal? type 'Int)
  (check-equal? (count-nodes 'UnionInject core) 0))

(test-case "全ての枝が Never の match は Never を返し、行は枝の行の和である"
  (match-define (list _ type _)
    (accepted (all-never-if-source)))
  (match type
    [`(NFn ,_ Int () ,row () User)
     (check-equal? row '(Suspend Partial))]
    [_ (fail-check (format "関数型の形が違う: ~s" type))])
  (check-equal?
   (rejected-code
    '(Fn ((s (NFn () Never (Suspend) ()))
          (p (NFn () Never (Partial) ())))
         Int (Suspend)
         (Let x
              (Eliminate (Construct true (Types))
                         ((true () -> (Apply s)) (false () -> (Apply p))))
              (Let (n const Never) x 0))))
   (code 'undeclared-function-effect)))

(test-case "Record の枝は helper で合流する"
  (match-define (list _ type _)
    (accepted
     `(Let x
          ,(if-source '(Rec ((a imm 1) (b imm (Construct true (Types)))))
                      '(Rec ((a imm 3) (c imm "s"))))
          x)))
  (check-equal? type '(Record ((a Int imm)))))

(test-case "合流できない Record の枝は type-mismatch で拒否する"
  (check-equal?
   (rejected-code
    `(Let x
         ,(if-source '(Rec ((a imm 1))) '(Rec ((a imm "s"))))
         x))
   (code 'type-mismatch)))

(test-case "Owned の枝が 2 種類ある match は type-mismatch で拒否する"
  (check-equal?
   (rejected-code
    '(Fn ((p (Owned Int)) (q (Owned String))) Unit ()
         (Let x
              (Eliminate (Construct true (Types))
                         ((true () -> (Move p)) (false () -> (Move q))))
              unit)))
   (code 'type-mismatch)))

(test-case "expected を必要とする枝の本体は先に拒否する"
  (check-equal?
   (rejected-code `(Let x ,(if-source '(Construct some 1) 1) x))
   (code 'eliminate-needs-expected-type)))

(test-case "枝の無名関数は 1 回だけ登録する"
  (match (elab/tag
          `(Let x
               ,(if-source '(Fn ((v Int)) Int () v)
                           '(Fn ((v Int)) Int () 1))
               x))
    [(list _ _ _ callables) (check-equal? (length callables) 2)]
    [other (fail-check (format "elaborate が拒否した: ~s" other))]))

(test-case "mode off の synth の Eliminate は従来どおり拒否する"
  (match (elab `(Let x ,(if-source 1 "s") x))
    [`(err ,d)
     (check-equal? (diagnostic-id d)
                   (code 'eliminate-needs-expected-type))]
    [other (fail-check (format "mode off で受理した: ~s" other))]))

(test-case "Record expected は欄関数の行だけが異なる Union を合流する"
  (define plain-function '(NFn (Int) Int () ()))
  (define partial-function '(NFn (Int) Int (Partial) ()))
  (define plain-record `(Record ((f ,plain-function imm))))
  (define partial-record `(Record ((f ,partial-function imm))))
  (void
   (accepted
    `(Fn ((u (Union ,plain-record ,partial-record)))
         ,partial-record () u))))

(test-case "Record expected は Absent optional 欄と Owned 欄を残して分解する"
  (define optional-member
    '(Record ((a Int imm) (o Int imm opt) (b Bool imm))))
  (define optional-other
    '(Record ((a Int imm) (o Int imm opt) (c String imm))))
  (define optional-target '(Record ((a Int imm) (o Int imm opt))))
  (define optional-union `(Union ,optional-member ,optional-other))
  (match-define
    (list optional-core _ _)
    (accepted
     `(Let (source const ,optional-member)
           (Rec ((a imm 1) (b imm (Construct true (Types)))))
           (Let (u const ,optional-union) source
                (Let (r let ,optional-target) u r)))))
  (check-equal? (count-nodes 'Absent optional-core) 1)
  (define owned-member
    '(Record ((a Int imm) (o (Owned Res) imm) (b Bool imm))))
  (define owned-other
    '(Record ((a Int imm) (o (Owned Res) imm) (c String imm))))
  (define owned-target '(Record ((a Int imm) (o (Owned Res) imm))))
  (define owned-union `(Union ,owned-member ,owned-other))
  (void
   (accepted
    `(Fn ((u ,owned-union)) ,owned-target ()
         (Let (r let ,owned-target) u r)))))

(test-case "Record expected rejects residual Owned and unmergeable common fields"
  (check-equal?
   (rejected-code
    '(Fn ((u (Union (Record ((a Int imm) (o (Owned Int) imm)))
                    (Record ((a Int imm) (c String imm))))))
         Int () (Let (r let (Record ((a Int imm)))) u 0)))
   (code 'type-mismatch))
  (check-equal?
   (rejected-code
    '(Fn ((u (Union (Record ((a Int imm) (b Int imm)))
                    (Record ((a Int imm) (b String imm))))))
         Int () (Let (r let (Record ((a Int imm)))) u 0)))
   (code 'type-mismatch)))

(test-case "Owned expected への Union 分解は型付け可能な成分である必要がある"
  ;; P2m2a の owned-union-member 制約により、実行可能な Union が Owned を
  ;; 直接の成分に持てない。よって decompose の Owned wrapper/Move 枝には
  ;; well-typed な入力経路がない。
  (check-equal?
   (rejected-code
    '(Fn ((p (Union (Owned Int) (Owned String)))) (Owned Int) () (Move p)))
   (code 'invalid-resolved-type)))
