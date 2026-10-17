#lang racket

(require rackunit
         racket/match
         "../classify.rkt"
         "../diagnostic.rkt"
         "../elaborate.rkt"
         "../erase.rkt")

(define (find-recur-context tree callables [environment '()])
  (match tree
    [`(Lam ,_ ,function (,parameters ...) ,body)
     (match (assoc function callables)
       [(list _ `(NFn (,parameter-types ...) ,_ ,_ ,_ ,_ ,_))
        (find-recur-context
         body callables
         (append (map list parameters parameter-types)
                 (list (list function (second (assoc function callables))))
                 environment))]
       [_ (find-recur-context body callables environment)])]
    [`(Let (,name ,_mode ,type) ,bound ,body)
     (or (find-recur-context bound callables environment)
         (find-recur-context body callables
                             (cons (if (eq? _mode 'mut)
                                       (list name type 'mut)
                                       (list name type))
                                   environment)))]
    [`(Recur ,_ ,_ ,_ ,_ ,_) (list tree environment)]
    [(? list? parts)
     (for/or ([part (in-list parts)])
       (find-recur-context part callables environment))]
    [_ #f]))

(define (strip-escape-rebuilds tree)
  (match tree
    [`(Perform ,operation
               (Let (,_ const ,_) ,payload
                 (Let (,_ const Unit) (Reassign ,_ ,_ ,_) ,_)))
     `(Perform ,operation ,(strip-escape-rebuilds payload))]
    [(? list? parts) (map strip-escape-rebuilds parts)]
    [_ tree]))

(define (flow-rebuild-recur condition)
  `(Fn ((values (List Int))
        (flag Bool)
        (g (NFn () Bool () ())))
       Int (Mutation)
       (Let (value mut (Record ((name String imm))))
            (Rec ((name imm "A") (id imm 1)))
         (NarrativeExpr
          (Eliminate ,condition
            ((true () ->
              (Let ignored
                   (Reassign value
                             (Rec ((name imm "B")
                                   (active imm (Construct true (Types))))))
                   (Recur loop ((rest (List Int))) Int (Return)
                     (Eliminate rest
                       ((nil () -> (Return 1))
                        (cons (head tail) -> (Apply loop tail))))
                     (Apply loop values))))
             (false () -> 0)))))))

(define (mutating-block-scrutinee-recur condition binding-mode)
  `(Fn ((values (List Int))
        (flag Bool)
        (g (NFn () Bool () ())))
       Int (Mutation)
       (Let (value ,binding-mode Int) 0
         (Recur loop ((rest (List Int))) Int (Return Mutation)
           (Let ignored
                (Eliminate
                 (Let block-result (Reassign value 1) ,condition)
                 ((true () -> unit)
                  (false () -> unit)))
             (Eliminate rest
               ((nil () -> (Return 0))
                (cons (head tail) -> (Apply loop tail)))))
           (Apply loop values)))))

(define (elaboration-error-id result)
  (match result
    [`(err ,diagnostic) (diagnostic-id diagnostic)]
    [_ #f]))

(test-case "captured mut の block scrutinee は変数と呼出しの両形で structural"
  (for ([condition (in-list '(flag (Apply g)))])
    (match (elab (mutating-block-scrutinee-recur condition 'mut))
      [(list core _type _row callables)
       (define found (find-recur-context (erase-core core) callables))
       (check-not-false found)
       (match-define (list recur environment) found)
       (match-define `(Recur ,callable ,function (,parameters ...) ,body ,_continuation)
         recur)
       (match-define `(NFn (,parameter-types ...) ,_ ,_ ,latent-row ,_ ,_)
         (second (assoc callable callables)))
       (define body-environment
         (append (map list parameters parameter-types)
                 (list (list function (second (assoc callable callables))))
                 environment))
       (check-false (memq 'Partial latent-row))
       (check-equal?
        (classify-recur-body function parameters body body-environment callables)
        '(Finite structural))]
      [other (fail-check
              (format "structural Recur の elaboration 成功を期待した: ~s" other))]))
  (check-equal?
   (elaboration-error-id (elab (mutating-block-scrutinee-recur 'flag 'const)))
   "E-VAR-011"))

(test-case "pending Return を含む Recur の分類は解決前後で structural"
  (for ([condition (in-list '(flag (Apply g)))])
    (match (elab (flow-rebuild-recur condition))
      [(list core _type _row callables)
       ;; Partial を宣言していないため、成功は elaboration 時の分類 gate が
       ;; Unknown でなく structural な再帰として受理したことを示す。
       (define found (find-recur-context (erase-core core) callables))
       (check-not-false found)
       (match-define (list recur environment) found)
       (match-define `(Recur ,callable ,function (,parameters ...) ,body ,_continuation)
         recur)
       (match-define `(NFn (,parameter-types ...) ,_ ,_ ,_ ,_ ,_)
         (second (assoc callable callables)))
       (match-define `(NFn ,_ ,_ ,_ ,latent-row ,_ ,_)
         (second (assoc callable callables)))
       ;; 成功した elab で Partial の無い自己再帰を通すため、Recur gate は
       ;; pending-escape の投影を structural と分類している。
       (check-false (memq 'Partial latent-row))
       (define body-environment
         (append (map list parameters parameter-types)
                 (list (list function (second (assoc callable callables))))
                 environment))
       (define body-classification
         (classify-recur-body function parameters body body-environment callables))
       (define projected-classification
         (classify-recur-body function parameters
                              (strip-escape-rebuilds body)
                              body-environment callables))
       ;; Pending Return は gate 時点で再構成前の Perform として分類される。
       ;; 同じ本体を解決後に分類しても、挿入された view 再構成を透過する。
       (check-equal? projected-classification '(Finite structural))
       (check-equal? body-classification '(Finite structural))
       (check-equal? (classify recur environment callables)
                     '(Finite structural))]
      [other (fail-check (format "elaboration success expected: ~s" other))])))
