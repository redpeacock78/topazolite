#lang racket

(require rackunit
         racket/match
         redex/reduction-semantics
         "../annotate.rkt"
         "../diagnostic.rkt"
         "../erase.rkt"
         "../lang.rkt"
         "../borrow.rkt"
         "../region.rkt"
         "../typing.rkt")

(define (id-of core places callables [environment '()])
  (diagnostic-id (core-type-of/diagnostic core places callables environment)))

(check-equal? (id-of 'x '() '()) "E-VAR-006")
(check-equal? (id-of '(Move 3) '() '()) "E-OWN-020")
(check-equal? (id-of '(Scope (3) 1) '() '()) "E-OWN-021")
(check-equal? (id-of '(PrimVal User no-such-prim) '() '()) "E-VAR-007")
(check-equal? (id-of '(Apply 1 2) '() '()) "E-APP-003")
(check-equal? (id-of '(Curry 1 2) '() '()) "E-APP-004")
(check-equal? (id-of '(Proj 1 a) '() '()) "E-RCD-007")
(check-equal? (id-of '(Rec ((a imm 1) (a imm 2))) '() '()) "E-RCD-006")
(check-equal? (id-of '(Eliminate 1 ()) '() '()) "E-DAT-006")
(check-equal? (id-of '(Lam User no-such-callable (x) x) '() '()) "E-APP-005")
(check-equal? (id-of '(Drop 1) '() '()) "E-OWN-011")
(check-equal? (id-of '(Error 0) '() '()) "E-TYP-016")
(check-equal? (core-check-row 1 '() '() 'String) #f)

;; 入口検査は 1 箇所にある。判定 API と診断 API が同じ入力集合を落とす。
(for ([bad (in-list (list (list '(NotACoreForm) '() '() '())
                          (list '(Construct (Union Int Int) nil) '() '() '())
                          (list 1 '() 'not-a-table '())
                          (list 1 'not-a-place-table '() '())
                          (list 1 '() '() 'not-an-environment)))])
  (match-define (list core places callables environment) bad)
  (check-false (core-check-row core places callables 'Int environment))
  (check-true (diagnostic?
               (core-type-of/diagnostic core places callables environment))))

(define callables '((f (NFn (Int) Int () ()))))
(let ([d (core-type-of/diagnostic
          '(Apply (Lam User f (x) x) "s")
          '()
          callables)])
  (check-equal? (diagnostic-id d) "E-TYP-023")
  (check-equal? (diagnostic-expected d) 'Int)
  (check-equal? (diagnostic-found d) 'String))

;; spanful な入力が spanless な入力と同じ判定を返す。
(define spanless '(Drop (resource 0)))
(define spanful
  '(Drop (#:span src 0 12) (resource (#:span src 6 11) 0)))
(define places '((0 Res)))

(check-equal? (core-type-of spanless places '())
              '(Unit (Own)))
(check-equal? (core-type-of spanful places '())
              '(Unit (Own)))

;; 入口検査は投影した形へ掛ける。spanful でも Core 外の形は落ちる。
(check-equal? (core-type-of '(NotACoreForm (#:span src 0 3)) places '())
              'ill-typed)

(define owned-environment '((x (Owned Res))))
(define move-source '(Move x))
(check-equal? (core-type-of move-source '() '() owned-environment)
              (core-type-of (annotate-core move-source)
                            '()
                            '()
                            owned-environment))
(check-equal? (core-type-of move-source '() '() owned-environment)
              '((Owned Res) (Own)))

(define handle-source
  '(Handle (Return boundary Int)
           (x -> x)
           1))
(check-equal? (core-type-of handle-source '() '())
              (core-type-of (annotate-core handle-source) '() '()))
(check-equal? (core-type-of (annotate-core handle-source) '() '())
              '(Int ()))

;; 失敗しても従来の返り値のまま返る。
(check-equal? (core-type-of '(Drop 1) '() '()) 'ill-typed)
(check-equal? (core-check-row '(Drop 1) '() '() 'Unit) #f)

;; 第 1 経路が成功する所有型の Drop。
(check-equal? (core-type-of '(Drop (resource 0)) '((0 Res)) '())
              '(Unit (Own)))

;; 第 1 経路の失敗を局所的に回復し、fallback の check-as へ進む。
(check-equal? (core-type-of '(Drop (Error 0)) '((0 Res)) '())
              '(Unit (Own)))

;; fallback も失敗したときは外側へ抜ける。
(check-equal? (core-type-of '(Drop 1) '((0 Res)) '()) 'ill-typed)

;; Task 8 では producer の全 key を、実際に到達する spanful な Core で
;; 1 回ずつ検査する。表の入力は G2+ の子を list で包まない形にそろえる。
(define (reach-span start end)
  (list '#:span 'src start end))
(define (reach-node head start end . children)
  (list* head (reach-span start end) children))
(define (reach-lit value start end)
  (list '#:lit value (reach-span start end)))
(define (reach-var name start end)
  (list '#:var name (reach-span start end)))
(define (reach-ty type start end)
  (list '#:ty type (reach-span start end)))
(define (reach-bind name start end)
  (list '#:bind name (reach-span start end)))
(define (reach-lbl label start end)
  (list '#:lbl label (reach-span start end)))
(define (reach-branch start end constructor names body)
  (list (reach-span start end)
        constructor
        (map (λ (name) (reach-bind name start end)) names)
        '->
        body))
(define (reach-row key core places callables environment expected-span
                   [make-Λ #f])
  (list key core places callables environment expected-span make-Λ))

(define (reach-region-ctx core)
  (region-ctx (build-region-ir (erase-core core)) '() (hash) (hash)))

(define reach-call-f '((f (NFn (Int) Int () ()))))
(define reach-call-opt '((f (NFn ((Option Int)) Int () ()))))
(define reach-call-obligation
  '((f (NFn (Int) Int () ((Prop NonEmpty))))))
(define reach-owned-environment '((x (Owned Res))))
(define reach-int-environment '((x Int)))
(define reach-record-a '(Record ((a Int imm))))
(define reach-list-int '(List Int))

;; concrete な親の寿命は、外側の位置へ広がれないため Reborrow の上限を破る。
;; IR と environment を同じ build の結果から作り、rho の所属を保つ。
(define reborrow-escape-core
  (reach-node 'Scope 1211 1260 '()
              (reach-node 'Yield 1219 1258
                          (reach-node 'Scope 1220 1230 '()
                                      (reach-lit 0 1225 1226))
                          (reach-node 'Reborrow 1231 1257
                                      (reach-var 'y 1240 1241)))))
(define reborrow-escape-ir
  (build-region-ir (erase-core reborrow-escape-core)))
(define reborrow-escape-rho
  (region->rho reborrow-escape-ir
               (region-at reborrow-escape-ir '(0 0))))
(define reborrow-escape-environment
  `((y (BorrowedMut Int ,reborrow-escape-rho))))
(define (reborrow-escape-region-ctx _core)
  (region-ctx reborrow-escape-ir '() (hash) (hash 'y (set 'x))))

;; producer が使う key 集合。未登録の key と登録したが未到達の key を
;; 別々に検査できるよう、ill-typed とも表へ残す。
(define producer-keys
  '(;; SYN
    not-core-term
    ;; TYP
    error-needs-expected-type incompatible-branch-types invalid-callables
    invalid-environment invalid-places non-normal-type
    non-normalizable-result-type type-mismatch
    ;; EFF
    effectful-curry-operand undeclared-function-effect
    ;; OWN
    drop-non-owned move-non-owned owned-constructor-field
    owned-curry-argument owned-function-parameter owned-record-field
    owned-refined-payload owned-untrusted-payload
    owned-variable-requires-move unknown-place unmanaged-place
    ;; VAR
    duplicate-branch-binder duplicate-parameter non-canonical-primitive
    unbound-variable unknown-primitive
    ;; APP
    apply-non-function curry-non-function unknown-callable
    ;; ARI
    arity-mismatch branch-binder-arity parameter-arity-mismatch
    ;; RCD
    const-record-residual duplicate-record-label project-non-record
    record-binding-incompatible unknown-record-label
    unmergeable-branch-records
    ;; DAT
    duplicate-branch-constructor non-data-eliminate non-exhaustive-eliminate
    unknown-constructor unknown-data-type
    ;; PRF
    discharge-obligation-count discharge-proposition-mismatch
    discharge-target-not-apply unsatisfied-proof-obligation
   ;; BOR
    borrowed-owned-payload borrow-region-mismatch
    borrow-conflicting-alias borrow-escapes-owner borrow-non-owned
    borrow-unknown-owner-region drop-borrowed move-borrowed
    reborrow-non-mutable reborrow-region-escapes
    borrowed-function-capture borrowed-function-parameter
    borrowed-function-result
    ;; default
    ill-typed))

(define reachability-table
  (list
   (reach-row 'not-core-term
              (reach-node 'NotACoreForm 0 3)
              '() '() '() (reach-span 0 3))
   (reach-row 'error-needs-expected-type
              (reach-node 'Error 4 5 0)
              '() '() '() (reach-span 4 5))
   (reach-row 'invalid-callables (reach-lit 1 10 11)
              '() 'not-a-table '() (reach-span 10 11))
   (reach-row 'invalid-environment (reach-lit 1 12 13)
              '() '() 'not-an-environment (reach-span 12 13))
   (reach-row 'invalid-places (reach-lit 1 14 15)
              'not-a-place-table '() '() (reach-span 14 15))
   (reach-row 'non-normal-type
              (reach-node 'Construct 16 20
                          (reach-ty '(Union Int Int) 17 19) 'nil)
              '() '() '() (reach-span 16 20))
   (reach-row 'incompatible-branch-types
              (reach-node 'Eliminate 21 45
                          (reach-node 'Construct 22 25
                                      (reach-ty reach-list-int 23 24)
                                      'nil)
                          (list
                           (reach-branch 26 29 'nil '() (reach-lit 1 27 28))
                           (reach-branch
                            30 44 'cons '(h t)
                            (reach-node 'Rec 35 43
                                        (list (list (reach-lbl 'a 36 37)
                                                    'imm
                                                    (reach-lit 1 38 39)))))))
              '() '() '() (reach-span 21 45))
   (reach-row 'type-mismatch
              (reach-node 'Let 46 60
                          (list (reach-bind 'x 47 48) 'const
                                (reach-ty reach-record-a 49 50))
                          (reach-lit 1 51 52)
                          (reach-var 'x 53 54))
              '() '() '() (reach-span 51 52))
   (reach-row 'type-mismatch
              (reach-node 'Apply 61 80
                          (reach-node 'Lam 62 69 'User 'f
                                      (list (reach-bind 'x 63 64))
                                      (reach-lit 1 65 66))
                          (reach-node 'Construct 70 78
                                      (reach-ty reach-list-int 71 72)
                                      'nil))
              '() reach-call-opt '() (reach-span 70 78))
   (reach-row 'type-mismatch
              (reach-node 'Apply 81 100
                          (reach-node 'Lam 82 89 'User 'f
                                      (list (reach-bind 'x 83 84))
                                      (reach-var 'x 85 86))
                          (reach-lit "s" 90 91))
              '() reach-call-f '() (reach-span 90 91))
   (reach-row 'undeclared-function-effect
              (reach-node 'Lam 101 115 'User 'f
                          (list (reach-bind 'x 102 103))
                          (reach-node 'Yield 108 114
                                      (reach-var 'x 109 110)
                                      (reach-var 'x 111 112)))
              '() reach-call-f '() (reach-span 108 114))
   (reach-row 'undeclared-function-effect
              (reach-node 'RecurVal 116 130 'f
                          (reach-bind 'loop 117 118)
                          (list (reach-bind 'x 119 120))
                          (reach-node 'Yield 123 129
                                      (reach-var 'x 124 125)
                                      (reach-var 'x 126 127)))
              '() reach-call-f '() (reach-span 123 129))
   (reach-row 'undeclared-function-effect
              (reach-node 'Recur 131 148 'f
                          (reach-bind 'loop 132 133)
                          (list (reach-bind 'x 134 135))
                          (reach-node 'Yield 139 145
                                      (reach-var 'x 140 141)
                                      (reach-var 'x 142 143))
                          (reach-var 'loop 146 147))
              '() reach-call-f '() (reach-span 139 145))
   (reach-row 'drop-non-owned
              (reach-node 'Drop 149 160 (reach-lit 1 153 154))
              '() '() '() (reach-span 153 154))
   (reach-row 'move-non-owned
              (reach-node 'Move 161 166 (reach-var 'x 163 164))
              '() '() reach-int-environment (reach-span 161 166))
   (reach-row 'owned-constructor-field
              (reach-node 'Construct 167 180
                          (reach-ty '(Option (Owned Res)) 168 170)
                          'some
                          (reach-node 'resource 174 179 0))
              '() '() '() (reach-span 167 180))
   (reach-row 'owned-function-parameter
              (reach-node 'Lam 181 190 'User 'f
                          (list (reach-bind 'x 182 183))
                          (reach-lit 1 186 187))
              '() '((f (NFn ((Owned Res)) Int () ()))) '()
              (reach-span 181 190))
   (reach-row 'owned-function-parameter
              (reach-node 'RecurVal 191 203 'f
                          (reach-bind 'loop 192 193)
                          (list (reach-bind 'x 194 195))
                          (reach-lit 1 199 200))
              '() '((f (NFn ((Owned Res)) Int () ()))) '()
              (reach-span 191 203))
   (reach-row 'owned-function-parameter
              (reach-node 'Recur 204 220 'f
                          (reach-bind 'loop 205 206)
                          (list (reach-bind 'x 207 208))
                          (reach-lit 1 211 212)
                          (reach-var 'loop 215 216))
              '() '((f (NFn ((Owned Res)) Int () ()))) '()
              (reach-span 204 220))
   (reach-row 'owned-record-field
              (reach-node 'Rec 221 235
                          (list (list (reach-lbl 'a 222 223) 'imm
                                      (reach-node 'resource 228 234 0))))
              '() '() '() (reach-span 228 234))
   (reach-row 'owned-refined-payload
              (reach-node 'RVal 236 250
                          (reach-node 'ProofRep 237 240 'User
                                      'TypeNarrativeCap)
                          (reach-node 'resource 244 249 0))
              '() '() '() (reach-span 244 249))
   (reach-row 'owned-untrusted-payload
              (reach-node 'UVal 251 260
                          (reach-node 'resource 255 259 0))
              '() '() '() (reach-span 255 259))
   (reach-row 'owned-variable-requires-move
              (reach-var 'x 261 262)
              '() '() reach-owned-environment (reach-span 261 262))
   (reach-row 'unknown-place (reach-node 'Move 263 268 3)
              '() '() '() (reach-span 263 268))
   (reach-row 'unknown-place
              (reach-node 'Apply 269 285
                          (reach-node 'Lam 270 276 'User 'f
                                      (list (reach-bind 'x 271 272))
                                      (reach-var 'x 273 274))
                          (reach-node 'Error 277 282 99))
              '() reach-call-f '() (reach-span 277 282))
   (reach-row 'unmanaged-place
              (reach-node 'Scope 286 295 '(3) (reach-lit 1 291 292))
              '() '() '() (reach-span 286 295))
   (reach-row 'unmanaged-place
              (reach-node 'Apply 296 312
                          (reach-node 'Lam 297 303 'User 'f
                                      (list (reach-bind 'x 298 299))
                                      (reach-var 'x 300 301))
                          (reach-node 'Scope 304 310 '(3)
                                      (reach-lit 1 308 309)))
              '() reach-call-f '() (reach-span 304 310))
   (reach-row 'duplicate-branch-binder
              (reach-node 'Eliminate 313 340
                          (reach-node 'Construct 314 317
                                      (reach-ty reach-list-int 315 316)
                                      'nil)
                          (list
                           (reach-branch 318 321 'nil '() (reach-lit 1 319 320))
                           (reach-branch 322 339 'cons '(x x)
                                         (reach-var 'x 333 334))))
              '() '() '() (reach-span 322 339))
   (reach-row 'duplicate-parameter
              (reach-node 'Lam 341 350 'User 'f
                          (list (reach-bind 'x 342 343)
                                (reach-bind 'x 344 345))
                          (reach-var 'x 347 348))
              '() '((f (NFn (Int Int) Int () ()))) '()
              (reach-span 341 350))
   (reach-row 'duplicate-parameter
              (reach-node 'RecurVal 351 363 'f
                          (reach-bind 'loop 352 353)
                          (list (reach-bind 'x 354 355)
                                (reach-bind 'x 356 357))
                          (reach-var 'x 359 360))
              '() '((f (NFn (Int Int) Int () ()))) '()
              (reach-span 351 363))
   (reach-row 'duplicate-parameter
              (reach-node 'Recur 364 380 'f
                          (reach-bind 'loop 365 366)
                          (list (reach-bind 'x 367 368)
                                (reach-bind 'x 369 370))
                          (reach-lit 1 373 374)
                          (reach-var 'loop 376 377))
              '() '((f (NFn (Int Int) Int () ()))) '()
              (reach-span 364 380))
   (reach-row 'non-canonical-primitive
              (reach-node 'PrimVal 381 387 'User 'lt)
              '() '() '() (reach-span 381 387))
   (reach-row 'unbound-variable (reach-var 'x 388 389)
              '() '() '() (reach-span 388 389))
   (reach-row 'unbound-variable
              (reach-node 'Move 390 396 (reach-var 'x 393 394))
              '() '() '() (reach-span 390 396))
   (reach-row 'unknown-primitive
              (reach-node 'PrimVal 397 403 'User 'no-such-prim)
              '() '() '() (reach-span 397 403))
   (reach-row 'apply-non-function
              (reach-node 'Apply 404 414 (reach-lit 1 405 406)
                          (reach-lit 2 410 411))
              '() '() '() (reach-span 405 406))
   (reach-row 'apply-non-function
              (reach-node 'Discharge 415 430
                          (reach-node 'ProofRep 416 419 'User
                                      'TypeNarrativeCap)
                          (reach-node 'Apply 420 429
                                      (reach-lit 1 421 422)
                                      (reach-lit 2 426 427)))
              '() '() '() (reach-span 421 422))
   (reach-row 'curry-non-function
              (reach-node 'Curry 431 438 (reach-lit 1 432 433)
                          (reach-lit 2 436 437))
              '() '() '() (reach-span 432 433))
   (reach-row 'curry-non-function
              (reach-node 'CurryVal 439 448 'User
                          (reach-lit 1 440 441)
                          (reach-lit 2 445 446))
              '() '() '() (reach-span 440 441))
   (reach-row 'owned-curry-argument
              (reach-node 'Curry 449 460
                          (reach-var 'g 450 451)
                          (reach-node 'resource 455 459 0))
              '() '() '((g (NFn ((Owned Res)) Unit () ())))
              (reach-span 455 459))
   (reach-row 'unknown-callable
              (reach-node 'Lam 461 470 'User 'missing
                          (list (reach-bind 'x 462 463))
                          (reach-var 'x 466 467))
              '() '() '() (reach-span 461 470))
   (reach-row 'unknown-callable
              (reach-node 'RecurVal 471 483 'missing
                          (reach-bind 'loop 472 473)
                          (list (reach-bind 'x 474 475))
                          (reach-var 'x 478 479))
              '() '() '() (reach-span 471 483))
   (reach-row 'unknown-callable
              (reach-node 'Recur 484 500 'missing
                          (reach-bind 'loop 485 486)
                          (list (reach-bind 'x 487 488))
                          (reach-var 'x 491 492)
                          (reach-var 'loop 496 497))
              '() '() '() (reach-span 484 500))
   (reach-row 'arity-mismatch
              (reach-node 'Apply 501 517
                          (reach-node 'Lam 502 508 'User 'f
                                      (list (reach-bind 'x 503 504))
                                      (reach-var 'x 506 507))
                          (reach-lit 1 510 511)
                          (reach-lit 2 513 514))
              '() reach-call-f '() (reach-span 501 517))
   (reach-row 'branch-binder-arity
              (reach-node 'Eliminate 518 546
                          (reach-node 'Construct 519 522
                                      (reach-ty reach-list-int 520 521)
                                      'nil)
                          (list
                           (reach-branch 523 526 'nil '()
                                         (reach-lit 1 524 525))
                           (reach-branch 527 545 'cons '()
                                         (reach-lit 1 536 537))))
              '() '() '() (reach-span 527 545))
   (reach-row 'parameter-arity-mismatch
              (reach-node 'Lam 547 556 'User 'f
                          (list (reach-bind 'x 548 549)
                                (reach-bind 'y 550 551))
                          (reach-var 'x 553 554))
              '() '((f (NFn (Int) Int () ()))) '()
              (reach-span 547 556))
   (reach-row 'parameter-arity-mismatch
              (reach-node 'RecurVal 557 569 'f
                          (reach-bind 'loop 558 559)
                          (list (reach-bind 'x 560 561)
                                (reach-bind 'y 562 563))
                          (reach-var 'x 565 566))
              '() '((f (NFn (Int) Int () ()))) '()
              (reach-span 557 569))
   (reach-row 'parameter-arity-mismatch
              (reach-node 'Recur 570 586 'f
                          (reach-bind 'loop 571 572)
                          (list (reach-bind 'x 573 574)
                                (reach-bind 'y 575 576))
                          (reach-var 'x 579 580)
                          (reach-var 'loop 583 584))
              '() '((f (NFn (Int) Int () ()))) '()
              (reach-span 570 586))
   (reach-row 'const-record-residual
              (reach-node 'Let 587 607
                          (list (reach-bind 'x 588 589) 'const
                                (reach-ty reach-record-a 590 591))
                          (reach-node 'Rec 592 604
                                      (list
                                       (list (reach-lbl 'a 593 594) 'imm
                                             (reach-lit 1 595 596))
                                       (list (reach-lbl 'b 597 598) 'imm
                                             (reach-lit 1 599 600))))
                          (reach-var 'x 605 606))
              '() '() '() (reach-span 592 604))
   (reach-row 'duplicate-record-label
              (reach-node 'Rec 608 617
                          (list
                           (list (reach-lbl 'a 609 610) 'imm
                                 (reach-lit 1 611 612))
                           (list (reach-lbl 'a 613 614) 'imm
                                 (reach-lit 2 615 616))))
              '() '() '() (reach-span 608 617))
   (reach-row 'project-non-record
              (reach-node 'Proj 618 627 (reach-lit 1 619 620)
                          (reach-lbl 'a 624 625))
              '() '() '() (reach-span 619 620))
   (reach-row 'record-binding-incompatible
              (reach-node 'Let 628 644
                          (list (reach-bind 'x 629 630) 'const
                                (reach-ty reach-record-a 631 632))
                          (reach-node 'Rec 633 641
                                      (list (list (reach-lbl 'b 634 635)
                                                  'imm
                                                  (reach-lit 1 636 637))))
                          (reach-var 'x 642 643))
              '() '() '() (reach-span 633 641))
   (reach-row 'unknown-record-label
              (reach-node 'Proj 645 656
                          (reach-node 'Rec 646 652
                                      (list (list (reach-lbl 'a 647 648)
                                                  'imm
                                                  (reach-lit 1 649 650))))
                          (reach-lbl 'b 653 654))
              '() '() '() (reach-span 645 656))
   (reach-row 'duplicate-branch-constructor
              (reach-node 'Eliminate 657 682
                          (reach-node 'Construct 658 661
                                      (reach-ty reach-list-int 659 660)
                                      'nil)
                          (list
                           (reach-branch 662 665 'nil '()
                                         (reach-lit 1 663 664))
                           (reach-branch 666 681 'nil '()
                                         (reach-lit 1 667 668))))
              '() '() '() (reach-span 657 682))
   (reach-row 'non-data-eliminate
              (reach-node 'Eliminate 683 702 (reach-lit 1 684 685) '())
              '() '() '() (reach-span 684 685))
   (reach-row 'non-exhaustive-eliminate
              (reach-node 'Eliminate 703 722
                          (reach-node 'Construct 704 707
                                      (reach-ty reach-list-int 705 706)
                                      'nil)
                          (list (reach-branch 708 721 'nil '()
                                               (reach-lit 1 709 710))))
              '() '() '() (reach-span 703 722))
   (reach-row 'unknown-constructor
              (reach-node 'Construct 723 735
                          (reach-ty reach-list-int 724 725)
                          'some
                          (reach-lit 1 730 731))
              '() '() '() (reach-span 723 735))
   (reach-row 'unknown-data-type
              (reach-node 'Construct 736 746
                          (reach-ty '(Owned Int) 737 739)
                          'nil)
              '() '() '() (reach-span 736 746))
   (reach-row 'discharge-obligation-count
              (reach-node 'Discharge 747 772
                          (reach-node 'ProofRep 748 751 'User
                                      'TypeNarrativeCap)
                          (reach-node 'Discharge 752 771
                                      (reach-node 'ProofRep 753 756 'User
                                                  'TypeNarrativeCap)
                                      (reach-node 'Apply 757 770
                                                  (reach-node 'Lam 758 764
                                                              'User 'f
                                                              (list (reach-bind 'x 759 760))
                                                              (reach-var 'x 762 763))
                                                  (reach-lit 1 767 768))))
              '() reach-call-obligation '() (reach-span 747 772))
   (reach-row 'discharge-proposition-mismatch
              (reach-node 'Discharge 773 792
                          (reach-node 'ProofRep 774 777 'User
                                      'ValidNarrativeTrait)
                          (reach-node 'Apply 778 791
                                      (reach-node 'Lam 779 785 'User 'f
                                                  (list (reach-bind 'x 780 781))
                                                  (reach-var 'x 783 784))
                                      (reach-lit 1 788 789)))
              '() reach-call-obligation '() (reach-span 773 792))
   (reach-row 'discharge-target-not-apply
              (reach-node 'Discharge 793 805
                          (reach-node 'ProofRep 794 797 'User
                                      'TypeNarrativeCap)
                          (reach-lit 1 802 803))
              '() reach-call-obligation '() (reach-span 802 803))
   (reach-row 'unsatisfied-proof-obligation
              (reach-node 'Apply 806 822
                          (reach-node 'Lam 807 813 'User 'f
                                      (list (reach-bind 'x 808 809))
                                      (reach-var 'x 811 812))
                          (reach-lit 1 817 818))
              '() reach-call-obligation '() (reach-span 806 822))
   (reach-row 'borrowed-owned-payload
              (reach-node 'Let 1000 1020
                          (list (reach-bind 'x 1001 1002) 'const
                                (reach-ty '(Borrowed (Owned Int) 0) 1003 1010))
                          (reach-lit 1 1011 1012)
                          (reach-var 'x 1013 1014))
              '() '() '() (reach-span 1000 1020))
   (reach-row 'borrow-region-mismatch
              (reach-node 'BorrowAt 1021 1030 0 (reach-var 'x 1026 1027))
              '() '() '() (reach-span 1021 1030))
   (reach-row 'borrow-conflicting-alias
              (reach-node 'Scope 1031 1070 '()
                          (reach-node 'Let 1032 1069
                                      (list (reach-bind 'x 1033 1034) 'let
                                            (reach-ty '(Owned Res) 1035 1036))
                                      (reach-node 'resource 1037 1038 1)
                                      (reach-node 'Yield 1039 1068
                                                  (reach-node 'BorrowMut 1040 1050
                                                              (reach-var 'x 1045 1046))
                                                  (reach-node 'BorrowMut 1051 1067
                                                              (reach-var 'x 1060 1061)))))
              '() '() '() (reach-span 1051 1067)
              reach-region-ctx)
   (reach-row 'borrow-escapes-owner
              (reach-node 'Borrow 1071 1080 (reach-var 'x 1076 1077))
              '() '() '((x (Owned Int))) (reach-span 1071 1080)
              (λ (core)
                (define ir (build-region-ir '(Scope () (Scope () 0))))
                (region-ctx ir '() (hash 'x (region-at ir '(0 0))) (hash))))
   (reach-row 'borrow-non-owned
              (reach-node 'Scope 1081 1100 '()
                          (reach-node 'Let 1082 1099
                                      (list (reach-bind 'x 1083 1084) 'let
                                            (reach-ty 'Int 1085 1086))
                                      (reach-lit 1 1087 1088)
                                      (reach-node 'Borrow 1089 1098
                                                  (reach-var 'x 1094 1095))))
              '() '() '() (reach-span 1089 1098)
              reach-region-ctx)
   (reach-row 'borrow-unknown-owner-region
              (reach-node 'Borrow 1101 1110 (reach-var 'x 1106 1107))
              '() '() '((x (Owned Int))) (reach-span 1101 1110))
   (reach-row 'drop-borrowed
              (reach-node 'Scope 1111 1150 '()
                          (reach-node 'Let 1112 1149
                                      (list (reach-bind 'x 1113 1114) 'let
                                            (reach-ty '(Owned Res) 1115 1116))
                                      (reach-node 'resource 1117 1118 1)
                                      (reach-node 'Yield 1119 1148
                                                  (reach-node 'Borrow 1120 1129
                                                              (reach-var 'x 1125 1126))
                                                  (reach-node 'Drop 1130 1147
                                                              (reach-var 'x 1140 1141)))))
              '() '() '() (reach-span 1140 1141)
              reach-region-ctx)
   (reach-row 'move-borrowed
              (reach-node 'Scope 1151 1190 '()
                          (reach-node 'Let 1152 1189
                                      (list (reach-bind 'x 1153 1154) 'let
                                            (reach-ty '(Owned Res) 1155 1156))
                                      (reach-node 'resource 1157 1158 1)
                                      (reach-node 'Yield 1159 1188
                                                  (reach-node 'Borrow 1160 1169
                                                              (reach-var 'x 1165 1166))
                                                  (reach-node 'Move 1170 1187
                                                              (reach-var 'x 1180 1181)))))
              '() '() '() (reach-span 1170 1187)
              reach-region-ctx)
   (reach-row 'reborrow-non-mutable
              (reach-node 'Scope 1191 1210 '()
                          (reach-node 'Reborrow 1192 1209
                                      (reach-lit 1 1200 1201)))
              '() '() '() (reach-span 1192 1209) reach-region-ctx)
   (reach-row 'reborrow-region-escapes
              reborrow-escape-core
              '() '() reborrow-escape-environment (reach-span 1231 1257)
              reborrow-escape-region-ctx)
   (reach-row 'borrowed-function-parameter
              (reach-node 'Lam 1261 1280 'User 'f
                          (list (reach-bind 'a 1265 1266))
                          (reach-lit 0 1270 1271))
              '() '((f (NFn ((Borrowed Int 0)) Int () ()))) '()
              (reach-span 1261 1280))
   (reach-row 'borrowed-function-result
              (reach-node 'Lam 1281 1300 'User 'f
                          (list (reach-bind 'a 1285 1286))
                          (reach-lit 0 1290 1291))
              '() '((f (NFn (Int) (Borrowed Int 0) () ()))) '()
              (reach-span 1281 1300))
   (reach-row 'borrowed-function-capture
              (reach-node 'Lam 1301 1320 'User 'f
                          (list (reach-bind 'a 1305 1306))
                          (reach-var 'y 1310 1311))
              '() reach-call-f '((y (Borrowed Int 0)))
              (reach-span 1301 1320))))

(test-case "typing の producer key 集合が registry v3 と一致する"
  (define registry-keys
    (for/list ([row (in-list diagnostic-registry)]
               #:when (eq? (diagnostic-code-phase row) 'typing))
      (diagnostic-code-key row)))
  (check-equal? (length producer-keys) 62)
  (check-equal? (sort producer-keys symbol<?)
                (sort registry-keys symbol<?)))

(test-case "typing の全到達可能 key が正しい primary-span を持つ"
  (for ([entry (in-list reachability-table)])
    (match-define (list key core places callables environment expected-span
                        make-Λ) entry)
    (if (eq? key 'not-core-term)
        (check-false (redex-match? G2m c (erase-core core))
                     "not-core-term の入力は G2m の c ではない")
        (check-true (redex-match? G2m c (erase-core core))
                    (format "~a の入力が G2m の c に属する" key)))
    (define diagnostic
      (if make-Λ
          (core-type-of/diagnostic core places callables environment
                                   (make-Λ core))
          (core-type-of/diagnostic core places callables environment)))
    (check-true (diagnostic? diagnostic)
                (format "~a が Diagnostic を返す" key))
    (when (diagnostic? diagnostic)
      (check-equal? (diagnostic-id diagnostic)
                    (diagnostic-code-of 'typing key)
                    (format "~a の code" key))
      (check-equal? (diagnostic-primary-span diagnostic)
                    expected-span
                    (format "~a の primary-span" key))))
  ;; 現行 G2m からは到達しない key は表から除くが、registry からは除かない。
  ;; effectful-curry-operand は G2m の NFn 値が空 row しか返さないため到達しない。
  ;; G5b の Borrowed と BorrowedMut も空 row を返すため、この理由は変わらない。
  ;; non-normalizable-result-type は Intersection を含む型を入口が拒むため到達しない。
  ;; G5b の Borrowed と BorrowedMut は normalize-type が扱えるため、この理由は変わらない。
  ;; unmergeable-branch-records は正常型同士の merge だけが走るため到達しない。
  (define unreachable-keys
    '(effectful-curry-operand
      non-normalizable-result-type
      unmergeable-branch-records))
  (check-equal? (sort (remove-duplicates (map first reachability-table))
                      symbol<?)
                (sort (remove* (cons 'ill-typed unreachable-keys)
                               producer-keys)
                      symbol<?))
  (define multi-site-keys
    '(unmanaged-place unknown-place type-mismatch
      unbound-variable apply-non-function curry-non-function
      unknown-callable parameter-arity-mismatch duplicate-parameter
      owned-function-parameter undeclared-function-effect))
  (for ([key (in-list multi-site-keys)])
    (check-true
     (>= (length (filter (λ (entry) (eq? (first entry) key))
                         reachability-table))
         2)
     (format "~a は位置ごとの行を持つ" key))))

(test-case "Drop の境界と公開 API が同じ失敗を保つ"
  (define nested
    (reach-node 'Drop 823 840
                (reach-node 'Drop 824 838 (reach-lit 1 832 833))))
  (check-equal?
   (diagnostic-primary-span
    (core-type-of/diagnostic nested '((0 Res)) '()))
   (reach-span 832 833))
  (define distinct-child
    (reach-node 'Apply 841 851
                (reach-lit 1 843 844)
                (reach-lit 1 847 848)))
  (check-equal?
   (diagnostic-primary-span
    (core-type-of/diagnostic distinct-child '() '()))
   (reach-span 843 844))
  (check-equal? (core-type-of '(Drop (resource 0)) '((0 Res)) '())
                '(Unit (Own)))
  (check-false (core-check-row '(Drop 1) '((0 Res)) '()
                               '(Unit (Own))))
  (check-false (core-check '(Drop 1) '((0 Res)) '()
                           '(Unit (Own)) '()))
  (check-false
   (config-ok? '(cfg (Drop 1)
                     ((0 (resource 0)))
                     ((0 Available))
                     ())
                '()
                '(Unit (Own))
                '())))

(test-case "typing の expected と found の分配を固定する"
  (define distribution-table
    (list
     (list 'type-mismatch
           (reach-node 'Apply 852 868
                       (reach-node 'Lam 853 859 'User 'f
                                   (list (reach-bind 'x 854 855))
                                   (reach-var 'x 857 858))
                       (reach-lit "s" 863 864))
           '() reach-call-f '() 'Int 'String)
     (list 'arity-mismatch
           (reach-node 'Apply 869 885
                       (reach-node 'Lam 870 876 'User 'f
                                   (list (reach-bind 'x 871 872))
                                   (reach-var 'x 874 875))
                       (reach-lit 1 878 879)
                       (reach-lit 2 881 882))
           '() reach-call-f '() 1 2)
     (list 'parameter-arity-mismatch
           (reach-node 'Lam 886 895 'User 'f
                       (list (reach-bind 'x 887 888)
                             (reach-bind 'y 889 890))
                       (reach-var 'x 892 893))
           '() '((f (NFn (Int) Int () ()))) '() 1 2)
     (list 'branch-binder-arity
           (reach-node 'Eliminate 896 924
                       (reach-node 'Construct 897 900
                                   (reach-ty reach-list-int 898 899)
                                   'nil)
                       (list
                        (reach-branch 901 904 'nil '()
                                      (reach-lit 1 902 903))
                        (reach-branch 905 923 'cons '()
                                      (reach-lit 1 914 915))))
           '() '() '() 2 0)
     (list 'undeclared-function-effect
           (reach-node 'Lam 925 939 'User 'f
                       (list (reach-bind 'x 926 927))
                       (reach-node 'Yield 932 938
                                   (reach-var 'x 933 934)
                                   (reach-var 'x 935 936)))
           '() reach-call-f '() '() '((Yield Int)))))
  (for ([entry (in-list distribution-table)])
    (match-define (list key core places callables environment expected found) entry)
    (define diagnostic
      (core-type-of/diagnostic core places callables environment))
    (check-equal? (diagnostic-expected diagnostic) expected)
    (check-equal? (diagnostic-found diagnostic) found)
    (check-not-equal? expected found
                      (format "~a の expected と found は異なる" key)))
  ;; details が空の key は両欄が #f、一要素の key は found だけを持つ。
  (define empty-details
    (core-type-of/diagnostic '(Error 0) '() '()))
  (check-false (diagnostic-expected empty-details))
  (check-false (diagnostic-found empty-details))
  (define one-detail
    (core-type-of/diagnostic 1 '() 'not-a-table))
  (check-false (diagnostic-expected one-detail))
  (check-equal? (diagnostic-found one-detail) 'not-a-table))

;; drop の callback は details を apply で素通しする。
;; Drop で包んでも expected/found は包まない場合と一致する。
;; この lambda へ details を組み替える処理が入ると、この試験が落ちる。
(test-case
 "Drop の内側で起きた type-mismatch は expected/found を変えない"
 (define callables '((f (NFn (Int) Int () ()))))
 (define inner '(Apply (Lam User f (x) x) "s"))
 (define bare (core-type-of/diagnostic inner '() callables '()))
 (define wrapped (core-type-of/diagnostic `(Drop ,inner) '() callables '()))
 ;; drop-non-owned へ振り替わっていないことを先に確かめる。
 ;; 棄却されるのは argument そのものではなく、その内側の実引数である。
 (check-equal? (diagnostic-id wrapped)
               (diagnostic-code-of 'typing 'type-mismatch))
 (check-equal? (diagnostic-expected wrapped) (diagnostic-expected bare))
 (check-equal? (diagnostic-found wrapped) (diagnostic-found bare))
 ;; 素通し経路が二重変換していないことを値でも押さえる。
 (check-equal? (diagnostic-expected wrapped) 'Int)
 (check-equal? (diagnostic-found wrapped) 'String))
