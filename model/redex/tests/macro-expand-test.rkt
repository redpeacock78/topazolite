#lang racket

(require rackunit
         redex/reduction-semantics
         "../span-core.rkt"
         "../erase.rkt"
         "../origins.rkt"
         "../typing.rkt"
         "../diagnostic.rkt"
         "../macro-expand.rkt"
         racket/set)

;; typing-span-test.rkt:21 の (Apply 1 2) が E-APP-003 になるのを
;; spanful な形へ写したものである。
(define ill-typed-core
  (list 'Apply '(#:span main 0 10)
        '(#:lit 1 (#:span main 1 2))
        '(#:lit 2 (#:span main 3 4))))

;; 0 引数マクロ bad の template を ill-typed-core と同じ形にする。
;; 展開すると template 由来の span がすべて合成 span へ配り直され、
;; 最上位の Apply の span が展開表の鍵になる。
;; macro-env の要素は macro-expand.rkt:19 の match-define が読む
;; 4 つ組 (nm s pattern template) である。
(define bad-typing-env
  (list (list 'bad '(#:span main 20 30) '() ill-typed-core)))

(test-case
 "G2+ の c が MacroCall を受ける"
 (define call
   '(MacroCall (#:span main 0 10) User twice
               ((#:lit 1 (#:span main 6 7)))))
 (check-true (redex-match? G2+ c call)))

(test-case
 "展開由来の Lam の origin を verify-origins が受ける"
 (define lam
   '(Lam (#:span #:synthetic 1 1)
         (Derived User (Expand twice))
         c0
         ((#:bind x (#:span #:synthetic 2 2)))
         (#:var x (#:span #:synthetic 3 3))))
 (check-equal? (verify-origins/diagnostic R0 lam) 'ok))

(test-case
 "Expand でない step を持つ Lam を verify-origins が拒む"
 (define lam
   '(Lam (#:span #:synthetic 1 1)
         (Derived User (Policy p0))
         c0
         ((#:bind x (#:span #:synthetic 2 2)))
         (#:var x (#:span #:synthetic 3 3))))
 (check-not-equal? (verify-origins/diagnostic R0 lam) 'ok))

(test-case
 "初期 origin 検査は MacroCall の実引数内の Lam を歩く"
 (define arg
   '(Lam (#:span #:synthetic 4 4)
         User c-arg
         ((#:bind x (#:span #:synthetic 5 5)))
         (#:var x (#:span #:synthetic 6 6))))
 (define call
   (list 'MacroCall '(#:span main 0 10) 'User 'twice (list arg)))
 (check-equal? (term (verify-initial-origins ,R0 ,call)) 'ok))

(test-case
 "未展開の MacroCall を持つ項は 3 つの入口が拒む"
 (define call '(MacroCall (#:span main 0 10) User m ()))
 (define body (list 'Apply '(#:span main 0 20) call call))
 (check-exn #rx"未展開の MacroCall" (lambda () (require-expanded! 'test body)))
 (check-exn #rx"未展開の MacroCall"
            (lambda () (core-type-of body '() (hash))))
 (check-exn #rx"未展開の MacroCall"
            (lambda () (core-check-row body '() (hash) 'Unit)))
 (check-exn #rx"未展開の MacroCall"
            (lambda () (term (verify-origins ,R0 ,body)))))

(test-case
 "MacroCall を含まない項は素通りする"
 (define body '(#:lit 1 (#:span main 0 1)))
 (check-not-exn (lambda () (require-expanded! 'test body))))

(test-case
 "MAC-001: 展開器が作った節点の診断は展開表から trace を引く"
 (define call '(MacroCall (#:span main 0 10) User bad ()))
 (define-values (out tbl ds) (expand-macros call bad-typing-env))
 (check-equal? ds '())
 (define d (core-type-of/diagnostic out '() '()
                                    #:expansion-context tbl))
 (check-not-equal? (diagnostic-expansion-trace d) '())
 (check-equal? (first (first (diagnostic-expansion-trace d))) 'bad))

(test-case
 "MAC-001: 展開を経ていない項の診断の expansion-trace は空である"
 (define d (core-type-of/diagnostic ill-typed-core '() '()))
 (check-equal? (diagnostic-expansion-trace d) '()))

(define s-def '(#:span main 0 20))
(define s-arg '(#:span main 8 9))

(test-case
 "妥当な定義は診断を出さない"
 (define defs (list (list 'twice s-def '(x) (list '#:var 'x s-arg))))
 (check-equal? (macro-env-errors defs) '()))

(test-case
 "同じ名前を 2 度定義すると E-MAC-003 を出す"
 (define s2 '(#:span main 30 50))
 (define defs (list (list 'twice s-def '(x) (list '#:var 'x s-arg))
                    (list 'twice s2 '(y) (list '#:var 'y '(#:span main 38 39)))))
 (define ds (macro-env-errors defs))
 (check-equal? (map diagnostic-id ds) '("E-MAC-003"))
 (check-equal? (diagnostic-primary-span (first ds)) s2)
 (check-equal? (map first (diagnostic-related (first ds))) '(previous-definition)))

(test-case
 "pattern に同じ変数が 2 度現れると E-MAC-005 を出す"
 (define defs (list (list 'twice s-def '(x x) (list '#:var 'x s-arg))))
 (check-equal? (map diagnostic-id (macro-env-errors defs)) '("E-MAC-005")))

(test-case
 "template が pattern に無い変数を参照すると E-MAC-006 を出す"
 (define s-free '(#:span main 12 13))
 (define defs (list (list 'twice s-def '(x) (list '#:var 'y s-free))))
 (define ds (macro-env-errors defs))
 (check-equal? (map diagnostic-id ds) '("E-MAC-006"))
 (check-equal? (diagnostic-primary-span (first ds)) s-free))

(test-case
 "template の Lam の origin が User でないと E-MAC-004 を出す"
 (define s-lam '(#:span main 10 18))
 (define defs
   (list (list 'twice s-def '(x)
               (list 'Lam s-lam '(Derived User (Expand other)) 'c0
                     (list (list '#:bind 'x '(#:span main 14 15)))
                     (list '#:var 'x '(#:span main 16 17))))))
 (define ds (macro-env-errors defs))
 (check-equal? (map diagnostic-id ds) '("E-MAC-004"))
 (check-equal? (diagnostic-primary-span (first ds)) s-lam))

(test-case
 "template の中の MacroCall の origin が User でないと E-MAC-004 を出す"
 (define s-call '(#:span main 10 18))
 (define defs
   (list (list 'twice s-def '(x)
               (list 'MacroCall s-call '(Reserved o-add) 'other
                     (list (list '#:var 'x '(#:span main 16 17)))))))
 (define ds (macro-env-errors defs))
 (check-equal? (map diagnostic-id ds) '("E-MAC-004"))
 (check-equal? (diagnostic-primary-span (first ds)) s-call))

;; n 段の自己再帰の macro-env を作る。m_i の template は
;; (Apply s (MacroCall s User m_{i+1} ())) であり、最後の m_n は
;; (#:lit 0 s) である。各段の Apply が展開結果の中に残る。
(define (self-env n)
  (for/list ([i (in-range 1 (add1 n))])
    (define nm (string->symbol (format "m~a" i)))
    (define s (list '#:span 'main (* i 10) (+ (* i 10) 5)))
    (define template
      (if (= i n)
          (list '#:lit 0 s)
          (list 'Apply s
                (list 'MacroCall s 'User
                      (string->symbol (format "m~a" (add1 i))) '()))))
    (list nm s '() template)))

(define (self-call)
  '(MacroCall (#:span main 0 5) User m1 ()))

;; 項の中の span をすべて前順で並べる。
(define (all-spans t)
  (cond
    [(and (list? t) (pair? t) (eq? (car t) '#:span)) (list t)]
    [(list? t) (append-map all-spans t)]
    [else '()]))

(define (synthetic-spans t)
  (filter (lambda (s) (eq? (second s) '#:synthetic)) (all-spans t)))

(define (has-macro-call? t)
  (cond
    [(and (list? t) (pair? t) (eq? (car t) 'MacroCall)) #t]
    [(list? t) (ormap has-macro-call? t)]
    [else #f]))

(define twice-env
  (list (list 'twice '(#:span main 0 20) '(x)
              '(Apply (#:span main 10 18)
                      (#:var x (#:span main 12 13))
                      (#:var x (#:span main 15 16))))))

(test-case
 "複数の実引数を pattern 順に対応させる"
 (define env
   (list (list 'pair '(#:span main 0 20) '(x y)
               '(Apply (#:span main 10 18)
                       (#:var x (#:span main 12 13))
                       (#:var y (#:span main 15 16))))))
 (define arg-x '(#:lit 1 (#:span main 30 31)))
 (define arg-y '(#:lit 2 (#:span main 32 33)))
 (define call (list 'MacroCall '(#:span main 20 28) 'User 'pair
                    (list arg-x arg-y)))
 (define-values (out _tbl ds) (expand-macros call env))
 (check-equal? ds '())
 ;; x と y を同じ位置へ置かないことで、引数の逆順化を検出する。
 (check-equal? (third out) arg-x)
 (check-equal? (fourth out) arg-y))

(test-case
 "CurryVal の origin は erase 後の形を保つ"
 (define origin
   '(Derived (Reserved o-add)
             (Curry (#:lit 1 (#:span main 90 91)))))
 (define function
   '(PrimVal (#:span main 1 2) (Reserved o-add) add))
 (define argument '(#:lit 1 (#:span main 3 4)))
 (define env
   (list (list 'keep '(#:span main 0 20) '()
               (list 'CurryVal '(#:span main 0 8) origin function argument))))
 (define call '(MacroCall (#:span main 30 40) User keep ()))
 (define-values (out _tbl ds) (expand-macros call env))
 (check-equal? ds '())
 ;; O の span が変わっても、erase 後の origin の形は変わらない。
 (check-equal? (erase-core (third out)) (erase-core origin))
 (check-equal? (verify-origins/diagnostic R0 out) 'ok))

(test-case
 "展開器は MacroCall を消し 3 つの値を返す"
 (define call '(MacroCall (#:span main 30 40) User twice
                          ((#:lit 1 (#:span main 36 37)))))
 (define-values (out tbl ds) (expand-macros call twice-env))
 (check-equal? ds '())
 (check-false (has-macro-call? out))
 (check-true (redex-match? G2+ c out)))

(test-case
 "引数由来の部分項の span は展開の前後で変わらない"
 (define s-arg2 '(#:span main 36 37))
 (define call (list 'MacroCall '(#:span main 30 40) 'User 'twice
                    (list (list '#:lit 1 s-arg2))))
 (define-values (out tbl ds) (expand-macros call twice-env))
 (check-equal? (length (filter (lambda (s) (equal? s s-arg2)) (all-spans out))) 2))

(test-case
 "展開表の鍵は展開器が割り当てた合成 span のうち結果に残ったものと一致する"
 (define call '(MacroCall (#:span main 30 40) User twice
                          ((#:lit 1 (#:span main 36 37)))))
 (define-values (out tbl ds) (expand-macros call twice-env))
 (check-equal? (list->set (hash-keys tbl))
               (list->set (synthetic-spans out))))

(test-case
 "一つの展開が作った合成 span は互いに異なる"
 (define call '(MacroCall (#:span main 30 40) User twice
                          ((#:lit 1 (#:span main 36 37)))))
 (define-values (out tbl ds) (expand-macros call twice-env))
 (define ss (synthetic-spans out))
 (check-equal? (length ss) (length (remove-duplicates ss))))

(test-case
 "入力がすでに合成 span を持っていても展開器の連番が重ならない"
 (define s-pre '(#:span #:synthetic 7 7))
 (define call (list 'MacroCall '(#:span main 30 40) 'User 'twice
                    (list (list '#:lit 1 s-pre))))
 (define-values (out tbl ds) (expand-macros call twice-env))
 (check-equal? ds '())
 ;; 引数の合成 span は鍵にならない。
 (check-false (hash-has-key? tbl s-pre))
 ;; 割り当てた span の k は 7 より大きい。
 (for ([k (in-list (hash-keys tbl))])
   (check-true (> (third k) 7))))

(test-case
 "registry に無いマクロを呼ぶと E-MAC-007 を出す"
 (define call '(MacroCall (#:span main 30 40) User missing ()))
 (define-values (out tbl ds) (expand-macros call twice-env))
 (check-equal? (map diagnostic-id ds) '("E-MAC-007"))
 (check-equal? (diagnostic-expansion-trace (first ds)) '()))

(test-case
 "実引数の個数が pattern と合わないと E-MAC-001 を出す"
 (define call '(MacroCall (#:span main 30 40) User twice ()))
 (define-values (out tbl ds) (expand-macros call twice-env))
 (check-equal? (map diagnostic-id ds) '("E-MAC-001")))

(test-case
 "入れ子の呼出しから出る診断は現在の trace を持つ"
 (define env
   (list (list 'outer '(#:span main 0 20) '()
               '(MacroCall (#:span main 10 18) User missing ()))))
 (define call '(MacroCall (#:span main 30 40) User outer ()))
 (define-values (out tbl ds) (expand-macros call env))
 (check-equal? (map diagnostic-id ds) '("E-MAC-007"))
 (check-equal? (length (diagnostic-expansion-trace (first ds))) 1)
 (check-equal? (first (first (diagnostic-expansion-trace (first ds)))) 'outer))

(test-case
 "起点の MacroCall の O が Derived だと E-MAC-004 を出す"
 (define call '(MacroCall (#:span main 30 40) (Derived User (Expand twice))
                          twice ((#:lit 1 (#:span main 36 37)))))
 (define-values (out tbl ds) (expand-macros call twice-env))
 (check-equal? (map diagnostic-id ds) '("E-MAC-004"))
 (check-false out)
 (check-equal? tbl (hash)))

(test-case
 "起点の MacroCall の O が Reserved だと E-MAC-004 を出す"
 (define call '(MacroCall (#:span main 30 40) (Reserved o-add)
                          twice ((#:lit 1 (#:span main 36 37)))))
 (define-values (out tbl ds) (expand-macros call twice-env))
 (check-equal? (map diagnostic-id ds) '("E-MAC-004"))
 (check-false out)
 (check-equal? tbl (hash)))

(test-case
 "macro-env が不正なら展開へ進まない"
 (define env (list (list 'twice '(#:span main 0 20) '(x x)
                         '(#:var x (#:span main 12 13)))))
 (define call '(MacroCall (#:span main 30 40) User twice
                          ((#:lit 1 (#:span main 36 37)))))
 (define-values (out tbl ds) (expand-macros call env))
 (check-equal? (map diagnostic-id ds) '("E-MAC-005"))
 (check-false out)
 (check-equal? tbl (hash)))

(test-case
 "深さ 32 まで展開し 33 段目で E-MAC-002 を出す"
 (define-values (out32 tbl32 ds32) (expand-macros (self-call) (self-env 32)))
 (check-equal? ds32 '())
 (check-false (has-macro-call? out32))
 ;; 展開表の鍵に stale なものが無い。
 (for ([k (in-list (hash-keys tbl32))])
   (check-not-false (member k (all-spans out32))))
 ;; もっとも深い節点の trace は 32 段である。
 (define depths (for/list ([v (in-hash-values tbl32)]) (length v)))
 (check-equal? (apply max depths) 32)
 ;; trace は外から内へ並ぶ。
 (define deepest
   (for/first ([v (in-hash-values tbl32)] #:when (= (length v) 32)) v))
 (check-equal? (first (first deepest)) 'm1)
 (check-equal? (first (last deepest)) 'm32)

 (define-values (out33 tbl33 ds33) (expand-macros (self-call) (self-env 33)))
 (check-equal? (map diagnostic-id ds33) '("E-MAC-002"))
 (check-equal? (length (diagnostic-expansion-trace (first ds33))) 32)
 ;; spec 6.4: 拒否の primary span は最も外側の呼出しである。
 (check-equal? (diagnostic-primary-span (first ds33)) '(#:span main 0 5))
 (check-false out33)
 (check-equal? tbl33 (hash)))

(test-case
 "spec 5.5: 根が pattern 変数である template では最上位が実引数由来になる"
 ;; identity(x) = x。template の根が (#:var x _) そのものである。
 (define env (list (list 'identity '(#:span main 0 16) '(x)
                         '(#:var x (#:span main 13 14)))))
 (define arg '(#:lit 7 (#:span main 30 31)))
 (define call (list 'MacroCall '(#:span main 20 32) 'User 'identity (list arg)))
 (define-values (out tbl ds) (expand-macros call env))
 (check-equal? ds '())
 ;; 展開結果は実引数そのものであり、span は書き換わらない。
 (check-equal? out arg)
 ;; 最上位へ配った合成 span は置換で消えるため、鍵は 1 つも残らない。
 ;; spec 7.1 の「割り当てた合成 span のうち結果に残ったもの」がこの形である。
 (check-equal? tbl (hash)))

(test-case
 "spec 8.1/8.2: template 由来の Lam の origin が Expand の連鎖になる"
 ;; outer() の template は Lam であり、その本体に inner() の呼出しを置く。
 ;; 展開器は outer を展開してから、その結果の中の inner を展開する。
 (define env
   (list
    (list 'inner '(#:span main 0 10) '()
          '(Lam (#:span main 2 9) User c-inner ((#:bind y (#:span main 5 6)))
                (#:var y (#:span main 7 8))))
    (list 'outer '(#:span main 20 40) '()
          '(Lam (#:span main 22 39) User c-outer ((#:bind z (#:span main 25 26)))
                (MacroCall (#:span main 28 38) User inner ())))))
 (define call '(MacroCall (#:span main 50 60) User outer ()))
 (define-values (out tbl ds) (expand-macros call env))
 (check-equal? ds '())
 (check-false (has-macro-call? out))
 (check-true (redex-match? G2+ c out))
 ;; 外側の Lam は起点の O が User であるから 1 段である。
 (check-equal? (third out) '(Derived User (Expand outer)))
 ;; 内側の MacroCall は outer の書き換えで O を受け取っており、その O を
 ;; 起点として inner が展開される。よって内側の Lam は 2 段の連鎖を持つ。
 (define inner-lam (sixth out))
 (check-equal? (first inner-lam) 'Lam)
 (check-equal? (third inner-lam)
               '(Derived (Derived User (Expand outer)) (Expand inner)))
 ;; 書き換えた origin が origins.rkt の検査を通る。
 (check-equal? (verify-origins/diagnostic R0 out) 'ok))
