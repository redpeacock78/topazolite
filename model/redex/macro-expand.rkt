#lang racket

;; macro.md §4: マクロ定義の並びの妥当性を検査する。macro-env は module の
;; 定数ではなく引数である（traits.rkt:54 の trait-table と同じ扱いである）。

(require redex/reduction-semantics
         "span-core.rkt"
         "span-subst.rkt"
         "diagnostic.rkt")

(provide macro-env-errors)

;; 定義の 4 つ組 (nm s pattern template) を受け、違反の診断を並べて返す。
;; 順序は定義の順、1 つの定義の中では §4.3 の 3 条件の順である。
(define (macro-env-errors defs)
  (for/fold ([seen (hash)] [out '()] #:result (reverse out))
            ([d (in-list defs)])
    (match-define (list nm s pattern template) d)
    (define dup
      (cond
        [(hash-ref seen nm #f)
         => (lambda (s_prev)
              (list (diagnostic-of 'expand 'macro-name-duplicate
                                   #:primary-span s
                                   #:related (list (list 'previous-definition s_prev
                                                         "先に現れた定義である")))))]
        [else '()]))
    (define pat-dup
      (if (= (length pattern) (length (remove-duplicates pattern)))
          '()
          (list (diagnostic-of 'expand 'macro-pattern-duplicate #:primary-span s))))
    ;; template の自由変数は pattern の変数に収まらなければならない。
    ;; 主 span は当該の (#:var x s) の span であるため、自由変数の名前では
    ;; なく出現節点を拾う。
    (define free-nodes (span-free-var-nodes template pattern))
    (define free-errs
      (for/list ([node (in-list free-nodes)])
        (diagnostic-of 'expand 'macro-template-free-var
                       #:primary-span (span-of node)
                       #:related (list (list 'macro-definition s "当該のマクロ定義である")))))
    ;; template の中の Lam と MacroCall の origin は User でなければならない。
    (define origin-errs
      (for/list ([node (in-list (user-origin-violations template))])
        (diagnostic-of 'expand 'macro-origin-invalid
                       #:primary-span (span-of node)
                       #:related (list (list 'macro-definition s "当該のマクロ定義である")))))
    (values (hash-set seen nm s)
            (append (reverse (append dup pat-dup free-errs origin-errs)) out))))

;; 前順で t の部分項を歩き、pred を満たす節点を並べて返す。
;; Task 5 の non-user-macro-calls と synthetic-spans-of も同じ走査を使う。
;; 前順という順序の約束を 1 箇所へ閉じ込めるため、走査を書くのはここだけである。
(define (nodes-where t pred)
  (append (if (pred t) (list t) '())
          (if (list? t)
              (append-map (lambda (u) (nodes-where u pred)) t)
              '())))

(define (macro-call? t)
  (match t [(list 'MacroCall _s _O _nm _args) #t] [_ #f]))

(define (lam-node? t)
  (match t [(list 'Lam _s _O _cid _binds _c) #t] [_ #f]))

;; Lam も MacroCall も第 3 要素が origin である
;; （span-core.rkt:136 と macro.md §5.1）。
(define (node-origin t) (third t))

;; template の中の Lam と MacroCall のうち、origin が User でない節点を
;; 前順で並べて返す。macro.md §4.3 の第 3 条件である。
(define (user-origin-violations term)
  (nodes-where term
               (lambda (t)
                 (and (or (lam-node? t) (macro-call? t))
                      (not (eq? (node-origin t) 'User))))))
