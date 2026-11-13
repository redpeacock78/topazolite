#lang racket

(require rackunit
         racket/list
         racket/match
         redex/reduction-semantics
         "../borrow.rkt"
         "../borrow-gen.rkt"
         "../borrow-oracle.rkt"
         "../annotate.rkt"
         "../diagnostic.rkt"
         "../driver.rkt"
         "../elaborate.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../lang.rkt"
         "../machine.rkt"
         "../region.rkt"
         "../typing.rkt")

(define simple-forall-callables
  '((len
     (ForallRegion (a)
       (NFn ((Borrowed Int (RParam a))) Int () () () User)))))

(define returning-forall-callables
  '((id
     (ForallRegion (a)
       (NFn ((Borrowed Int (RParam a)))
            (Borrowed Int (RParam a)) () () () User)))
    (idm
     (ForallRegion (a)
       (NFn ((BorrowedMut Int (RParam a)))
            (BorrowedMut Int (RParam a)) () () () User)))))

(define field-forward-type
  '(ForallRegion (a)
     (NFn ((Record ((a (Borrowed Int (RParam a)) imm))))
          (Borrowed Int (RParam a)) () () () User)))

(define field-maker-type
  '(ForallRegion (a)
     (NFn ((Borrowed Int (RParam a)))
          (Record ((a (Borrowed Int (RParam a)) imm))) () () () User)))

(define field-forward-callables
  `((field ,field-forward-type)
    (make ,field-maker-type)))

(define field-forward-value
  '(RegionLam (a)
     (Lam User field (p) (Proj p a))))

(define field-maker-value
  '(RegionLam (a)
     (Lam User make (p) (Rec ((a imm p))))))

(define (field-forward-core kind escape?)
  (define argument-type '(Record ((a (Borrowed Int 0) imm))))
  (define argument-expression
    (case kind
      [(variable literal) '(Rec ((a imm (Borrow owner))))]
      [(call-result)
       '(Apply make (Borrow owner))]
      [else (error 'field-forward-core "unknown input kind: ~s" kind)]))
  (define (apply-field actual)
    `(Apply (Proj holder h) ,actual))
  `(Scope ()
     (Let (owner let (Owned Int)) 7
       (Let (holder const (Record ((h ,field-forward-type imm))))
            (Rec ((h imm ,field-forward-value)))
         ,(if (eq? kind 'call-result)
              `(Let (make const ,field-maker-type) ,field-maker-value
                 ,(if escape?
                      (apply-field argument-expression)
                      `(Let (value const Int)
                         (Read ,(apply-field argument-expression)) 0)))
              (if (eq? kind 'variable)
                  `(Let (item let ,argument-type) ,argument-expression
                     ,(if escape?
                          (apply-field 'item)
                          `(Let (value const Int)
                             (Read ,(apply-field 'item)) 0)))
                  (if escape?
                      (apply-field argument-expression)
                      `(Let (value const Int)
                         (Read ,(apply-field argument-expression)) 0))))))))

(define simple-forall-call
  '(Scope ()
     (Let (owner let (Owned Int)) 7
       (Let (result const Int)
            (Apply
             (RegionLam (a)
               (Lam User len (p) (Read p)))
             (Borrow owner))
         (Assign (BorrowMut owner) 8)))))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [fuel 300])
    (when (zero? fuel)
      (error 'trace-g2 "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() configs]
      [(list (list _ next))
       (loop next (append configs (list next)) (sub1 fuel))]
      [steps (error 'trace-g2 "一意な次状態でない: ~s" steps)])))

(define (collect-annotated-regions form term)
  (match term
    [`(RegionApp ,callee (,rhos ...))
     (append (if (eq? form 'RegionApp) rhos '())
             (collect-annotated-regions form callee)
             (append-map (lambda (rho) (collect-annotated-regions form rho))
                         rhos))]
    [`(BorrowAt ,rho ,owner ,w)
     (append (if (eq? form 'BorrowAt) (list rho) '())
             (collect-annotated-regions form owner)
             (collect-annotated-regions form w))]
    [(? pair? pair)
     (append (collect-annotated-regions form (car pair))
             (collect-annotated-regions form (cdr pair)))]
    [_ '()]))

(define (check-runtime-trace core callables expected)
  (define ir (build-region-ir core))
  (define typed (core-type-of/regions core '() callables #:ir ir))
  (check-true (region-typed? typed)
              (format "region 型付け成功を期待: ~s" typed))
  (when (region-typed? typed)
    (define configs
      (trace-g2 (inject-g2m (region-execution-core typed))))
    (for ([config (in-list configs)] [index (in-naturals)])
      (define row (runtime-row config callables expected #:region-ir ir))
      (check-not-false row (format "config ~a の runtime-row" index))
      (when row
        (check-true (config-ok? config callables expected row #:region-ir ir)
                    (format "config ~a の config-ok?" index))))
    (check-true
     (redex-match? G2m v (match (last configs) [`(cfg ,v ,_ ...) v]))
     "trace 終端が値")))

(define (field-forward-source kind [escape? #f])
  (string-append
   "fn get(p: {a: &Int}) -> &Int ! {Own, Partial} { return p.a }\n"
   (if (eq? kind 'call-result)
       "fn pack(p: &Int) -> {a: &Int} ! {Own, Partial} { return {a: p} }\n"
       "")
   "let holder = {h: get}\n"
   (if escape?
       (string-append
        "fn bad() -> Unit ! {Own, Partial} {\n"
        "  let result = { let owner: Owned<Int> = 7\n"
        "    holder.h({a: &owner}) }\n"
        "  ()\n}\n0")
       (string-append
        "let owner: Owned<Int> = 7\n"
        (case kind
          [(variable) "let item = {a: &owner}\nderef(holder.h(item))"]
          [(literal) "deref(holder.h({a: &owner}))"]
          [(call-result) "deref(holder.h(pack(&owner)))"]
          [else (error 'field-forward-source "unknown input kind: ~s" kind)])))))

(define (check-compiled-runtime-trace compiled kind)
  (define core (compiled-core compiled))
  (define callables (compiled-callables compiled))
  (define ir (build-region-ir core))
  (define typed (core-type-of/regions core '() callables #:ir ir))
  (check-true (region-typed? typed)
              (format "Surface 由来 Core の region 型付け成功: ~s" typed))
  (when (region-typed? typed)
    (check-true (pair? (collect-annotated-regions
                        'RegionApp (compiled-execution-core compiled)))
                "driver の実行 Core に暗黙 RegionApp がある")
    (define start (inject-g2m (erase-core (region-execution-core typed))))
    (define configs (trace-g2 start))
    (define expected (region-typed-type typed))
    (for ([config (in-list configs)] [index (in-naturals)])
      (define row (runtime-row config callables expected #:region-ir ir))
      (check-not-false row (format "Surface trace config ~a runtime-row" index))
      (when row
        (check-true (config-ok? config callables expected row #:region-ir ir)
                    (format "Surface trace config ~a config-ok?" index))))
    (check-equal?
     (check-borrow-execution start (region-typed-sidecar typed)
                             ir 300 (make-bcounters))
     'ok
     "Surface trace borrow oracle")))

(define (fill-scope-region core annotation-point)
  (define ir (build-region-ir core))
  (define rho (region->rho ir (region-at ir annotation-point)))
  (define filled
    (let replace ([term core])
      (match term
        [`(Borrowed Int 0) `(Borrowed Int ,rho)]
        [(? pair?) (cons (replace (car term)) (replace (cdr term)))]
        [_ term])))
  (values ir filled))

(test-case "len(&x) の直後は owner を書け、RegionApp は R2、BorrowAt は R3"
  (define ir (build-region-ir simple-forall-call))
  (define typed
    (core-type-of/regions simple-forall-call '()
                          simple-forall-callables #:ir ir))
  (check-true (region-typed? typed)
              (format "region 型付け成功を期待: ~s" typed))
  (match-define (list `(RVar ,alpha-index))
    (hash-ref (region-typed-implicit-region-apps typed) '(0 1 0)))
  (define instantiated-rho
    (region->rho ir (hash-ref (region-typed-σ typed) alpha-index)))
  (check-equal? instantiated-rho
                (region->rho ir (region-at ir '(0 1 0))))
  (check-not-equal? instantiated-rho
                    (region->rho ir (region-at/temporary ir '(0 1 0))))
  (define machine-core (region-execution-core typed))
  (check-equal? (first (collect-annotated-regions 'RegionApp machine-core))
                instantiated-rho)
  (check-equal? (first (collect-annotated-regions 'BorrowAt machine-core))
                (region->rho ir (region-at/temporary ir '(0 1 0))))
  (check-runtime-trace simple-forall-call simple-forall-callables 'Unit))

(test-case "返された借用は owner の Scope を越えない"
  (define core
    '(Scope ()
       (Let (owner let (Owned Int)) 7
         (Apply
          (RegionLam (a) (Lam User id (p) p))
          (Borrow owner)))))
  (define-values (ir filled) (fill-scope-region core '(0 1)))
  (define typed (core-type-of/regions filled '()
                                      returning-forall-callables #:ir ir))
  (check-false (region-typed? typed)
               (format "短い owner からの借用戻りは拒否: ~s" typed))
  (check-true (diagnostic? typed))
  (check-equal? (diagnostic-id typed) "E-BOR-004"))

(test-case "返した共有借用の生存中は owner を書き換えられない"
  (define core
    '(Scope ()
       (Let (owner let (Owned Int)) 7
         (Let (r let (Borrowed Int 0))
              (Apply (RegionLam (a) (Lam User id (p) p))
                     (Borrow owner))
           (Let (written const Unit) (Assign (BorrowMut owner) 8)
             (Read r))))))
  (define-values (ir filled) (fill-scope-region core '(0 1 0)))
  (define typed (core-type-of/regions filled '()
                                      returning-forall-callables #:ir ir))
  (check-false (region-typed? typed)
               (format "借用中の owner write は拒否: ~s" typed))
  (check-true (diagnostic? typed))
  (check-equal? (diagnostic-id typed) "E-BOR-003"))

(test-case "返した可変借用の生存中は owner を読めない"
  (define core
    '(Scope ()
       (Let (owner let (Owned Int)) 7
         (Let (r let (BorrowedMut Int 0))
              (Apply (RegionLam (a) (Lam User idm (p) p))
                     (BorrowMut owner))
           (Let (seen const Int) (Read (Borrow owner))
             (Read r))))))
  (define-values (ir filled) (fill-scope-region core '(0 1 0)))
  (define typed (core-type-of/regions filled '()
                                      returning-forall-callables #:ir ir))
  (check-false (region-typed? typed)
               (format "可変借用中の owner read は拒否: ~s" typed))
  (check-true (diagnostic? typed))
  (check-equal? (diagnostic-id typed) "E-BOR-003"))

(for ([kind (in-list '(variable literal call-result))])
  (test-case
   (case kind
     [(variable) "summary の無い callee が record 変数の欄の借用を結果へ渡す"]
     [(literal) "summary の無い callee が record literal の欄の借用を結果へ渡す"]
     [(call-result) "summary の無い callee が関数結果の欄の借用を結果へ渡す"])
   (define accepted
     (compile-source/string 'src (field-forward-source kind)))
   (check-true (compiled? accepted)
               (format "Surface source を compile: ~s" accepted))
   (when (compiled? accepted)
     (check-true (pair? (collect-annotated-regions
                         'RegionApp (compiled-execution-core accepted)))
                 "Surface 由来の実行 Core に暗黙 RegionApp がある")
     (check-compiled-runtime-trace accepted kind))
   (define escaping
     (compile-source/string 'src (field-forward-source kind #t)))
   (check-true (diagnostic? escaping)
               (format "owner の Scope を越える欄の借用は拒否: ~s" escaping))
   (when (diagnostic? escaping)
     (check-equal? (diagnostic-id escaping) "E-BOR-004"))))

(test-case "Loop の借用 binder は暗黙実体化後に全 trace を通る"
  (define source
    '(Let (owner let (Owned Int)) 7
       (Apply
        (Fn ((p (Owned Int))) Int (Own)
          (LexicalScope
           (Let (x let (Owned Int)) (Move p)
             (Let (borrowed let (Borrowed Int Omitted)) (Borrow x)
               (Loop loop ((b (Borrowed Int Omitted))) Int ()
                     (Read b) (borrowed))))))
        (Move owner))))
  (match (elab (annotate-surface source))
    [(list core _type _row callables)
     (check-runtime-trace core callables 'Int)
     (define ir (build-region-ir core))
     (define typed (core-type-of/regions core '() callables #:ir ir))
     (when (region-typed? typed)
       (check-equal?
        (check-borrow-execution
         (inject-g2m (erase-core (region-execution-core typed)))
         (region-typed-sidecar typed) ir 300 (make-bcounters))
        'ok
        "Loop の全 trace が borrow oracle を通る"))]
    [`(err ,diagnostic)
     (fail (format "Loop の elab が拒否: ~s" diagnostic))]))
