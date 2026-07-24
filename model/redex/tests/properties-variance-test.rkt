#lang racket

(require rackunit
         "../compat.rkt"
         "../gen.rkt"
         "../type-equiv.rkt"
         "properties-test.rkt")

;; ---------------------------------------------------------------------------
;; Preservation 回帰: elaboration は全型 compat? で受理するのに、⊢core の
;; check-as が type-equiv? へ落ちると、簡約途中の Lam 値（callables 署名は
;; 互換だが非同値の NFn）で型付けが破れる。
;; ---------------------------------------------------------------------------

;; VAR-003: 注釈型の imm field は narrow-arg を受ける NFn を要求し、
;; 実 record は wide-arg（任意 record）を受ける Fn を格納する。
(define proj-variance-source
  '(Let (x const (Record ((f (NFn ((Record ((a Int imm)))) Int () ()) imm))))
        (Rec ((f imm (Fn ((r (Record ()))) Int () 7))))
        (Proj x f)))

;; VAR-001: 高階 Apply。callback 引数の注釈は narrow-arg を受ける NFn、
;; 実引数は wide-arg を受ける Fn（互換だが非同値）。
(define apply-variance-source
  '(Apply (Fn ((callback (NFn ((Record ((a Int imm)))) Int () ())))
              Int ()
              (Apply callback (Rec ((a imm 1)))))
          (Fn ((r (Record ()))) Int () 7)))

(test-case "VAR-003: imm field の互換非同値関数を Proj する Preservation 回帰"
  (check-true (preservation-g2? proj-variance-source)))

(test-case "VAR-001: 互換非同値関数を渡す高階 Apply の Preservation 回帰"
  (check-true (preservation-g2? apply-variance-source)))

;; ---------------------------------------------------------------------------
;; 性質 1〜5。plain seeded loop（redex-check は項生成用なので使わない）。
;; 各性質は空洞化対策の counter を持ち、0 件なら fail する。
;; ---------------------------------------------------------------------------

(define limits (read-bounds))
(define attempts (bounds-attempts limits))
(define type-depth 3)

(test-case "VAR-001: 性質1 compat? の反射性"
  (call-with-search-seed
   limits
   (lambda ()
     (for ([_i (in-range attempts)])
       (define t (random-variance-type type-depth))
       (check-true (compat? t t))))))

(test-case "VAR-001: 性質1 compat? の推移性（narrow 連鎖）"
  (call-with-search-seed
   limits
   (lambda ()
     (define chain-count (box 0))
     (for ([_i (in-range attempts)])
       (define c (random-variance-type type-depth))
       (define b (narrow-variance-type c))
       (define a (narrow-variance-type b))
       (when (and (compat? a b) (compat? b c))
         (set-box! chain-count (add1 (unbox chain-count)))
         (check-true (compat? a c))))
     (check-true (positive? (unbox chain-count)))
     (printf "性質1 推移性: attempts=~a chains=~a seed=~a\n"
             attempts (unbox chain-count) (bounds-seed limits)))))

(test-case "VAR-001: 性質1 引数位置を跨ぐ推移性（構成的連鎖）"
  (call-with-search-seed
   limits
   (lambda ()
     (define strict-count (box 0))
     (for ([_i (in-range attempts)])
       (define payload (random-variance-type 2))
       ;; f-a <: f-b <: f-c を引数反変・返り値共変・E/Q 包含すべてが
       ;; 効く形で構成する。
       (define f-a `(NFn ((Record ())) Never () ()))
       (define f-b `(NFn ((Record ((a ,payload imm)))) Int
                         ((Yield ,payload)) ()))
       (define f-c `(NFn ((Record ((a ,payload imm) (b Bool imm)))) Int
                         ((Yield ,payload) Suspend) (ValidNarrativeTrait)))
       (check-true (compat? f-a f-b))
       (check-true (compat? f-b f-c))
       (check-true (compat? f-a f-c))
       (unless (or (type-equiv? f-a f-b) (type-equiv? f-b f-c))
         (set-box! strict-count (add1 (unbox strict-count)))))
     (check-true (positive? (unbox strict-count)))
     (printf "性質1 構成的連鎖: attempts=~a strict=~a seed=~a\n"
             attempts (unbox strict-count) (bounds-seed limits)))))

(test-case "VAR-002: 性質2 type-equiv? は compat? を含意する"
  (call-with-search-seed
   limits
   (lambda ()
     (define pair-count (box 0))
     (for ([_i (in-range attempts)])
       (define base (random-variance-type type-depth))
       (define permuted (permute-variance-type base))
       (check-true (type-equiv? base permuted))
       (when (not (equal? base permuted))
         (set-box! pair-count (add1 (unbox pair-count)))
         (check-true (compat? base permuted))
         (check-true (compat? permuted base)))
       ;; 独立ペア: 偶然一致した同値も compat? へ持ち上がる
       (define other (random-variance-type type-depth))
       (when (type-equiv? base other)
         (check-true (compat? base other))))
     (check-true (positive? (unbox pair-count)))
     (printf "性質2: attempts=~a permuted-pairs=~a seed=~a\n"
             attempts (unbox pair-count) (bounds-seed limits)))))

(test-case "VAR-003: 性質3 mut field は関数 variance を透過しない"
  (define sub-fn '(NFn ((Record ())) Int () ()))
  (define sup-fn '(NFn ((Record ((a Int imm)))) Int () ()))
  ;; 前提の固定: このペアは互換だが同値でない
  (check-true  (compat? sub-fn sup-fn))
  (check-false (type-equiv? sub-fn sup-fn))
  ;; 共通 imm field があっても mut field が非同値なら record は非互換
  (check-false (compat? '(Record ((s Int imm) (f Never mut)))
                        '(Record ((s Int imm) (f Int mut)))))
  (check-false (compat? `(Record ((s Int imm) (f ,sub-fn mut)))
                        `(Record ((s Int imm) (f ,sup-fn mut))))))

(test-case "VAR-001: 性質4 方向健全性（widen は一方向）"
  (call-with-search-seed
   limits
   (lambda ()
     (define strict-count (box 0))
     (for ([_i (in-range attempts)])
       (define t (random-variance-type type-depth))
       (define wider (widen-variance-type t))
       (check-true (compat? t wider))
       (unless (type-equiv? t wider)
         (set-box! strict-count (add1 (unbox strict-count)))
         (check-false (compat? wider t))))
     (check-true (positive? (unbox strict-count)))
     (printf "性質4: attempts=~a strict=~a seed=~a\n"
             attempts (unbox strict-count) (bounds-seed limits))))
  ;; 固定の逆向き反例: 各成分を単独で逆向きにすると拒否される
  (check-false (compat? '(NFn ((Record ((a Int imm)))) Int () ())
                        '(NFn ((Record ())) Int () ())))
  (check-false (compat? '(NFn () Int () ()) '(NFn () Never () ())))
  (check-false (compat? '(NFn () Int (Own) ()) '(NFn () Int () ())))
  (check-false (compat? '(NFn () Int () (ValidNarrativeTrait))
                        '(NFn () Int () ()))))

(test-case "VAR-003: 性質5 各経路の実効性（6 counter）"
  (call-with-search-seed
   limits
   (lambda ()
     (define arg-contra (box 0))
     (define return-cov (box 0))
     (define effect-strict (box 0))
     (define obligation-strict (box 0))
     (define imm-nfn-accept (box 0))
     (define mut-nfn-reject (box 0))
     (for ([_i (in-range attempts)])
       (define payload (random-variance-type 2))
       ;; 引数反変だけが効く受理
       (define arg-sub `(NFn ((Record ())) ,payload () ()))
       (define arg-sup `(NFn ((Record ((a Int imm)))) ,payload () ()))
       (check-true (compat? arg-sub arg-sup))
       (set-box! arg-contra (add1 (unbox arg-contra)))
       ;; 返り値共変だけが効く受理
       (check-true (compat? `(NFn (,payload) Never () ())
                            `(NFn (,payload) Int () ())))
       (set-box! return-cov (add1 (unbox return-cov)))
       ;; E の真部分集合（受理と逆向き拒否の対）
       (check-true  (compat? '(NFn () Int (Suspend) ())
                             '(NFn () Int (Suspend Own) ())))
       (check-false (compat? '(NFn () Int (Suspend Own) ())
                             '(NFn () Int (Suspend) ())))
       (set-box! effect-strict (add1 (unbox effect-strict)))
       ;; Q の真部分集合（受理と逆向き拒否の対）
       (check-true  (compat? '(NFn () Int () (ValidNarrativeTrait))
                             '(NFn () Int () (ValidNarrativeTrait
                                              TypeNarrativeCap))))
       (check-false (compat? '(NFn () Int () (ValidNarrativeTrait
                                              TypeNarrativeCap))
                             '(NFn () Int () (ValidNarrativeTrait))))
       (set-box! obligation-strict (add1 (unbox obligation-strict)))
       ;; imm field の NFn は variance を透過して受理
       (check-true (compat? `(Record ((f ,arg-sub imm)))
                            `(Record ((f ,arg-sup imm)))))
       (set-box! imm-nfn-accept (add1 (unbox imm-nfn-accept)))
       ;; mut field の NFn は互換非同値でも拒否
       (check-false (compat? `(Record ((f ,arg-sub mut)))
                             `(Record ((f ,arg-sup mut)))))
       (set-box! mut-nfn-reject (add1 (unbox mut-nfn-reject))))
     ;; 生成空間全体での narrow 健全性
     (for ([_i (in-range attempts)])
       (define top (random-variance-type type-depth))
       (check-true (compat? (narrow-variance-type top) top)))
     (check-true (positive? (unbox arg-contra)))
     (check-true (positive? (unbox return-cov)))
     (check-true (positive? (unbox effect-strict)))
     (check-true (positive? (unbox obligation-strict)))
     (check-true (positive? (unbox imm-nfn-accept)))
     (check-true (positive? (unbox mut-nfn-reject)))
     (printf "性質5: attempts=~a arg=~a return=~a E=~a Q=~a imm=~a mut=~a seed=~a\n"
             attempts (unbox arg-contra) (unbox return-cov)
             (unbox effect-strict) (unbox obligation-strict)
             (unbox imm-nfn-accept) (unbox mut-nfn-reject)
             (bounds-seed limits)))))
