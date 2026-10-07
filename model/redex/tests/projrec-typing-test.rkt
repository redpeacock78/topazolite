#lang racket

;; [REQ: SUR-006] 多 field 射影の型付け。
;; Surface は Owned 型を綴れない（surface.md §7.2.1）ため、lowering の出力
;; （surface-lower.rkt の SProjRec 節）と同じ形を Typed Core で組んで検査する。

(require rackunit
         racket/list
         racket/match
         racket/set
         redex/reduction-semantics
         "../borrow.rkt"
         "../gen.rkt"
         "../lang.rkt"
         "../machine.rkt"
         "../region.rkt"
         "../type-shape.rkt"
         "../type-equiv.rkt"
         "../typing.rkt")

;; 余剰の Owned 欄と、mut の欄を持つ record である。
(define r-type '(Record ((x (Owned Res) imm) (y Int imm) (z Int mut))))

(define (projected-result-type labels)
  (normalize-type
   `(Record
     ,(for/list ([label (in-list labels)])
        (match label
          ['x `(x (Owned Res) imm)]
          ['y '(y Int imm)]
          ['z '(z Int imm)])))))

;; lowering の出力に elaborate が型注釈を付けたあとの形である。
;; 受け側の place は消費せず、結果の欄はすべて imm である。
(define (projrec labels receiver)
  `(Rec ,(for/list ([l (in-list labels)])
           `(,l imm (Proj ,receiver ,l)))))

(define (with-record body result-type)
  `(Lam User projection-check (raw)
     (Handle (Return boundary ,result-type)
             (return-value -> return-value)
             (Scope ()
               (Let (r let ,r-type) raw ,body)))))

(define (projected labels)
  (with-record (projrec labels 'r) (projected-result-type labels)))

(define (result-of core [environment '()])
  (define callables
    (match core
      [`(Lam User projection-check (raw)
          (Handle (Return boundary ,return-type) ,_handler (Scope () ,_body)))
       `((projection-check (NFn (,r-type) ,return-type () (Own) () User)))]
      [_ '()]))
  (match (type-of/raw core '() callables environment
                      (empty-region-ctx))
    [(list 'ok
           (list `(NFn ,_parameters ,result-type ,_latent-in ,_latent-row
                       ,_obligations ,_origin)
                 _row))
     result-type]
    [(list 'ok (list type _row)) type]
    [(list 'fail key _node _details ...) key]))

;; spec §6.4。選んだ欄だけを持つ record になり、型の row は正規形になる。
(test-case "選んだ欄だけの record になる"
  (check-equal? (result-of (projected '(y)))
                '(Record ((y Int imm)))))

(test-case "欄の型は row の正規形になる"
  (check-equal? (result-of (projected '(z y)))
                '(Record ((y Int imm) (z Int imm)))))

;; spec §6.4。元が mut でも結果は imm である。
(test-case "mut の欄も結果では imm になる"
  (check-equal? (result-of (projected '(z)))
                '(Record ((z Int imm)))))

;; spec §6.5。残す label に Owned があると T-Rec が拒否する。
(test-case "Owned の欄を射影すると移動必須で拒否する"
  (check-equal? (result-of (projected '(x y)))
                'owned-variable-requires-move))

;; spec §6.6。余剰の Owned 欄を残さない射影は、narrowing ではないので
;; Proof を要求しない。r は const で束縛するだけで move されない。
(test-case "余剰の Owned 欄を落とす射影は Proof を要求しない"
  (check-equal? (result-of (projected '(y z)))
                '(Record ((y Int imm) (z Int imm)))))

;; 射影のあとも r をそのまま使える。
(test-case "射影は受け側を消費しない"
  (check-equal?
   (result-of
    (with-record
     `(Let (q const (Record ((y Int imm))))
          ,(projrec '(y) 'r)
        (Proj r y))
     'Int))
   'Int))

(define resource-record-type
  '(Record ((a Int imm)
            (optional Int imm opt)
            (owner (Option (Owned Res)) imm))))
(define resource-record-value
  '(Rec ((a imm 41)
         (optional imm (Absent Int))
         (owner imm
                (Construct (Option (Owned Res)) some
                           (OwnLeaf (resource 13)))))))
(define resource-record-present-value
  '(Rec ((a imm 41)
         (optional imm 53)
         (owner imm
                (Construct (Option (Owned Res)) some
                           (OwnLeaf (resource 13)))))))
(define nested-resource-record-type
  `(Record ((n ,resource-record-type imm))))
(define nested-resource-record-value
  `(Rec ((n imm ,resource-record-value))))
(define nested-resource-record-present-value
  `(Rec ((n imm ,resource-record-present-value))))

(define (resource-let body)
  `(Let (x let ,resource-record-type) ,resource-record-value ,body))
(define (resource-let/value value body)
  `(Let (x let ,resource-record-type) ,value ,body))

(define (run-g2-value core)
  (match (run-g2 (inject-g2m core) 300)
    [`(cfg ,value ,_heap ,_states ,_tokens ,_trace) value]
    [other (error 'run-g2-value "unexpected configuration: ~s" other)]))

(define (initial core)
  (define (to-runtime-value value)
    (match value
      [`(OwnLeaf (resource ,number))
       `(OwnedLeaf (tok ,number) (resource ,number))]
      [(? list? parts) (map to-runtime-value parts)]
      [_ value]))
  (define (owned-tokens value)
    (match value
      [`(OwnedLeaf ,token ,_payload) (list (list token 'Available))]
      [(? list? parts) (append-map owned-tokens parts)]
      [_ '()]))
  (define runtime-core (to-runtime-value core))
  `(cfg (Scope () ,runtime-core) () () ,(owned-tokens runtime-core) ()))

(define (g2-trace core)
  (define start (initial core))
  (let loop ([current start] [configs (list start)] [rules '()] [fuel 80])
    (when (zero? fuel)
      (error 'g2-trace "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() (values configs rules)]
      [(list (list rule next))
       (loop next (append configs (list next)) (append rules (list rule))
             (sub1 fuel))]
      [steps (error 'g2-trace "一意な次状態を期待したが複数ある: ~s" steps)])))

(define (checked-run-g2-value core)
  (define expected
    (match (type-of/raw core '() '() '() (empty-region-ctx))
      [(list 'ok (list type _row)) type]
      [other (error 'checked-run-g2-value "型付けに失敗した: ~s" other)]))
  (define-values (configs _rules) (g2-trace core))
  (define rows
    (for/list ([config (in-list configs)] [index (in-naturals)])
      (define row (runtime-row config '() expected))
      (check-not-false row
                       (format "runtime row を得られない config ~a: ~s"
                               index config))
      (check-true (config-ok? config '() expected row)
                  (format "不正な中間 config ~a: ~s" index config))
      row))
  (for ([before (in-list rows)] [after (in-list (cdr rows))]
        [index (in-naturals)])
    (check-true (row-subset? after before)
                (format "config ~a から次の config で row が増えた: ~s -> ~s"
                        index before after)))
  (match (last configs)
    [`(cfg ,value ,_heap ,_states ,_tokens ,_trace) value]
    [other (error 'checked-run-g2-value "予期しない終端状態: ~s" other)]))

(test-case "資源型の Let 変数から非資源型の欄を読める"
  (check-equal? (result-of (resource-let '(Proj x a))) 'Int)
  (check-equal?
   (result-of (resource-let '(Rec ((a imm (Proj x a))
                                   (optional imm
                                     (ProjOpt Int x optional))))))
    '(Record ((a Int imm) (optional (Option Int) imm))))
  (check-equal? (checked-run-g2-value (resource-let '(Proj x a))) 41)
  (check-equal?
   (checked-run-g2-value (resource-let '(ProjOpt Int x optional)))
   '(Construct (Option Int) none))
  (check-equal?
   (checked-run-g2-value
    (resource-let/value resource-record-present-value
                        '(ProjOpt Int x optional)))
   '(Construct (Option Int) some 53)))

(test-case "資源型の欄は射影せず、射影後も record 全体を Move できる"
  (define moved
    (checked-run-g2-value
     (resource-let '(Let (n const Int) (Proj x a) (Move x)))))
  (check-equal?
   (result-of (resource-let '(Proj x owner)))
   'owned-variable-requires-move)
  (check-true (redex-match? G2m v moved)))

(test-case "非変数の資源型 record を多 field 射影しても停止しない"
  (define projection
    `(Let (%projrec const ,resource-record-type)
          ,resource-record-value
          (Rec ((a imm (Proj %projrec a))
                (optional imm (ProjOpt Int %projrec optional))))))
  (check-equal?
   (result-of projection)
   '(Record ((a Int imm) (optional (Option Int) imm))))
  (check-equal?
   (checked-run-g2-value projection)
   '(Rec ((a imm 41)
          (optional imm (Construct (Option Int) none))))))

(test-case "P の資源型 record から入れ子射影を一度に読む"
  (define core
    `(Let (z let ,nested-resource-record-type)
          ,nested-resource-record-value
          (Proj (Proj z n) a)))
  (check-equal? (result-of core) 'Int)
  (check-equal? (checked-run-g2-value core) 41)
  (define-values (_configs rules) (g2-trace core))
  (check-equal? (count (lambda (rule) (eq? rule 'R-ProjPlace)) rules) 1)
  (check-false (member 'R-ProjOptPlace rules))
  (check-not-false (member 'R-ProjPlace rules)))

(test-case "最外の ProjOpt を資源型 place の入れ子 path として読む"
  (define core
    `(Let (z let ,nested-resource-record-type)
          ,nested-resource-record-value
          (ProjOpt Int (Proj z n) optional)))
  (check-equal? (result-of core) '(Option Int))
  (check-equal? (checked-run-g2-value core)
                '(Construct (Option Int) none))
  (check-equal?
   (checked-run-g2-value
    `(Let (z let ,nested-resource-record-type)
          ,nested-resource-record-present-value
          (ProjOpt Int (Proj z n) optional)))
   '(Construct (Option Int) some 53)))

(test-case "入れ子 path の末端も資源型なら Move 必須で拒否する"
  (define core
    `(Let (z let ,nested-resource-record-type)
          ,nested-resource-record-value
          (Proj (Proj z n) owner)))
  (check-equal? (result-of core) 'owned-variable-requires-move))

(test-case "place でない record receiver の入れ子射影は通常の Proj で還元する"
  (define plain-inner-type '(Record ((a Int imm))))
  (define plain-outer-type `(Record ((n ,plain-inner-type imm))))
  (define plain-outer-value '(Rec ((n imm (Rec ((a imm 41)))))))
  (define core `(Proj (Proj ,plain-outer-value n) a))
  (check-equal? (result-of core) 'Int)
  (check-equal? (checked-run-g2-value core) 41)
  (define-values (_configs rules) (g2-trace core))
  (check-equal? (count (lambda (rule) (eq? rule 'R-Proj)) rules) 2)
  (check-false (member 'R-ProjPlace rules))
  (check-equal?
   (result-of `(Proj (Proj (Apply nested-source unit) n) a)
              `((nested-source
                 (NFn (Unit) ,nested-resource-record-type () (Own) () User))))
   'Int))

(test-case "入れ子の射影 path は重なる可変借用とだけ競合する"
  (define core
    `(Let (x let ,nested-resource-record-type)
          ,nested-resource-record-value
          (Proj (Proj x n) a)))
  (define ir (build-region-ir core))
  (define Λ (region-ctx ir '() (hash) (hash)))
  (define requests (fourth (typing-inference core '() '() '() Λ)))
  (define projection-use (findf use-request? requests))
  (define root (region-at ir '()))
  (define (check-conflict path)
    (let/ec escape
      (check-borrows
       ir (hash) (empty-psi)
       (cons (borrow-request 'x path 'mut root root core) requests)
       (lambda (_sigma rho) rho)
       (lambda (key _node) (escape key)))
      'ok))
  (check-equal? (use-request-fp projection-use) '(n a))
  (check-equal? (check-conflict '(n)) 'borrow-conflicting-use)
  (check-equal? (check-conflict '(n a)) 'borrow-conflicting-use)
  (check-equal? (check-conflict '(n owner)) 'ok))

(test-case "資源型欄の読みは label path を持ち、同じ欄の mut 借用と競合する"
  (define (check-projection core label other-label)
    (define ir (build-region-ir core))
    (define Λ (region-ctx ir '() (hash) (hash)))
    (define requests (fourth (typing-inference core '() '() '() Λ)))
    (define projection-use (findf use-request? requests))
    (define root (region-at ir '()))
    (define (check-conflict path)
      (let/ec escape
        (check-borrows
         ir (hash) (empty-psi)
         (cons (borrow-request 'x path 'mut root root core) requests)
         (lambda (_sigma rho) rho)
         (lambda (key _node) (escape key)))
        'ok))
    (check-equal? (use-request-w projection-use) 'x)
    (check-equal? (use-request-fp projection-use) (list label))
    (check-equal? (check-conflict (list label)) 'borrow-conflicting-use)
    (check-equal? (check-conflict (list other-label)) 'ok))
  (check-projection (resource-let '(Proj x a)) 'a 'optional)
  (check-projection (resource-let '(ProjOpt Int x optional))
                    'optional 'a))
