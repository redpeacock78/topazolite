#lang racket

(require racket/match
         racket/set
         redex/reduction-semantics
         "core-binding.rkt"
         "pr-lang.rkt")

(provide pr-variable? pr-free-vars pr-subst* pr-alpha-equivalent?)

(define (pr-variable? value)
  (redex-match? PR px value))

(define (pr-free-vars pc)
  (unless (redex-match? PR pc pc)
    (raise-argument-error 'pr-free-vars "PR pc" pc))
  (define (without names values)
    (set-subtract values (list->set names)))
  (define (branch-free-vars branch)
    (match branch
      [`(,_ (,names ...) -> ,body)
       (without names (walk body))]))
  (define (walk term)
    (match term
      [`(PLam (,names ...) ,body) (without names (walk body))]
      [`(PClosure ((,names ,values) ...) (,parameters ...) ,body)
       (set-union (for/fold ([free (set)]) ([value (in-list values)])
                    (set-union free (walk value)))
                  (without (append names parameters) (walk body)))]
      [`(PLet ,name ,bound ,body)
       (set-union (walk bound) (without (list name) (walk body)))]
      [`(PLetOwned ,name ,bound ,body)
       (set-union (walk bound) (without (list name) (walk body)))]
      [`(PLetrec ,name ,bound ,body)
       (without (list name) (set-union (walk bound) (walk body)))]
      [`(PApp ,callee ,arguments ...)
       (for/fold ([free (set)]) ([child (in-list (cons callee arguments))])
         (set-union free (walk child)))]
      [`(PTagged ,_ ,children ...)
       (for/fold ([free (set)]) ([child (in-list children)])
         (set-union free (walk child)))]
      [`(PRec ((,_ ,values) ...))
       (for/fold ([free (set)]) ([value (in-list values)])
         (set-union free (walk value)))]
      [`(PRecRewrite ,input ((,_ ,name ,body) ...))
       (for/fold ([free (walk input)]) ([name (in-list name)] [body (in-list body)])
         (set-union free (without (list name) (walk body))))]
      [`(PRecRemove ,record ,_) (walk record)]
      [`(PProj ,record ,_) (walk record)]
      [`(PProjOpt ,_ ,_ ,record ,_) (walk record)]
      [`(PMatch ,scrutinee (,branches ...))
       (for/fold ([free (walk scrutinee)]) ([branch (in-list branches)])
         (set-union free (branch-free-vars branch)))]
      [`(PPrim ,_ ,arguments ...)
       (for/fold ([free (set)]) ([argument (in-list arguments)])
         (set-union free (walk argument)))]
      [`(PEffect ,_ ,payload) (walk payload)]
      [`(PInstall ,_ ,handler ,body) (set-union (walk handler) (walk body))]
      [`(PRuntime ,_ ,arguments ...)
       (for/fold ([free (set)]) ([argument (in-list arguments)])
         (set-union free (walk argument)))]
      [`(PScopeExit ,_ ,body) (walk body)]
      [`(PError ,_) (set)]
      [`(PResource ,_) (set)]
      [`(PPlace ,_) (set)]
      [(? symbol? name) (if (pr-variable? name) (set name) (set))]
      [(or (? exact-integer?) (? string?)) (set)]
      [other (error 'pr-free-vars "不正な PR 項: ~s" other)]))
  (walk pc))

(define (pr-subst* pc binders replacement-values)
  (if (or (not (redex-match? PR pc pc))
          (not (list? binders))
          (not (list? replacement-values))
          (not (= (length binders) (length replacement-values)))
          (not (andmap pr-variable? binders))
          (not (= (length binders) (length (remove-duplicates binders eq?))))
          (not (andmap (lambda (value) (redex-match? PR pv value))
                       replacement-values)))
      #f
      (let ()
        (define forbidden
          (for/fold ([all (raw-symbols pc)]) ([value (in-list replacement-values)])
            (set-union all (raw-symbols value))))
        (define counter 0)
        (define (fresh-name base)
          (let loop ()
            (define candidate (string->symbol (format "~a«~a»" base counter)))
            (set! counter (add1 counter))
            (if (set-member? forbidden candidate)
                (loop)
                (begin
                  (set! forbidden (set-add forbidden candidate))
                  candidate))))
        (define mappings (map cons binders replacement-values))
        (define (remove-mappings names active)
          (filter (lambda (entry) (not (memq (car entry) names))) active))
        (define (replace-variable name active)
          (if (pr-variable? name)
              (let ([entry (assq name active)]) (if entry (cdr entry) name))
              name))
        (define (scope-subst-many bodies names active)
          (define active* (remove-mappings names active))
          (define inserted-free
            (for/fold ([free (set)]) ([entry (in-list active*)])
              (set-union free (pr-free-vars (cdr entry)))))
          (define-values (names* bodies*)
            (for/fold ([renamed-names names] [current-bodies bodies])
                      ([name (in-list names)] [index (in-naturals)])
              (if (set-member? inserted-free name)
                  (let ([fresh (fresh-name name)])
                    (values (for/list ([candidate (in-list renamed-names)]
                                       [i (in-naturals)])
                              (if (= i index) fresh candidate))
                            (map (lambda (body)
                                   (walk body (list (cons name fresh))))
                                 current-bodies)))
                  (values renamed-names current-bodies))))
          (values names* (map (lambda (body) (walk body active*)) bodies*)))
        (define (scope-subst body names active)
          (define-values (names* bodies*)
            (scope-subst-many (list body) names active))
          (values names* (first bodies*)))
        (define (subst-branch branch active)
          (match branch
            [`(,constructor (,names ...) -> ,body)
             (define-values (names* body*) (scope-subst body names active))
             `(,constructor ,names* -> ,body*)]))
        (define (walk term active)
          (match term
            [`(PLam (,parameters ...) ,body)
             (define-values (parameters* body*)
               (scope-subst body parameters active))
             `(PLam ,parameters* ,body*)]
            [`(PClosure ((,keys ,values) ...) (,parameters ...) ,body)
             (define-values (names* body*)
               (scope-subst body (append keys parameters) active))
             (define key-count (length keys))
             `(PClosure ,(for/list ([key (in-list (take names* key-count))]
                                    [value (in-list values)])
                           (list key (walk value active)))
                        ,(drop names* key-count)
                        ,body*)]
            [`(PLet ,name ,bound ,body)
             (define-values (names* body*) (scope-subst body (list name) active))
             `(PLet ,(first names*) ,(walk bound active) ,body*)]
            [`(PLetOwned ,name ,bound ,body)
             (define-values (names* body*) (scope-subst body (list name) active))
             `(PLetOwned ,(first names*) ,(walk bound active) ,body*)]
            [`(PLetrec ,name ,bound ,body)
             (define-values (names* bodies*)
               (scope-subst-many (list bound body) (list name) active))
             `(PLetrec ,(first names*) ,(first bodies*) ,(second bodies*))]
            [`(PApp ,callee ,arguments ...)
             `(PApp ,(walk callee active) ,@(map (lambda (arg) (walk arg active)) arguments))]
            [`(PTagged ,tag ,children ...)
             `(PTagged ,tag ,@(map (lambda (child) (walk child active)) children))]
            [`(PRec ((,labels ,values) ...))
             `(PRec ,(for/list ([label (in-list labels)] [value (in-list values)])
                       (list label (walk value active))))]
            [`(PRecRewrite ,input ((,labels ,names ,bodies) ...))
             `(PRecRewrite ,(walk input active)
                           ,(for/list ([label (in-list labels)]
                                       [name (in-list names)]
                                       [body (in-list bodies)])
                              (define-values (names* body*)
                                (scope-subst body (list name) active))
                              (list label (first names*) body*)))]
            [`(PRecRemove ,record ,labels) `(PRecRemove ,(walk record active) ,labels)]
            [`(PProj ,record ,label) `(PProj ,(walk record active) ,label)]
            [`(PProjOpt ,tag-a ,tag-b ,record ,label)
             `(PProjOpt ,tag-a ,tag-b ,(walk record active) ,label)]
            [`(PMatch ,scrutinee (,branches ...))
             `(PMatch ,(walk scrutinee active)
                      ,(map (lambda (branch) (subst-branch branch active)) branches))]
            [`(PPrim ,name ,arguments ...)
             `(PPrim ,name ,@(map (lambda (arg) (walk arg active)) arguments))]
            [`(PEffect ,pop ,payload) `(PEffect ,pop ,(walk payload active))]
            [`(PInstall ,pop ,handler ,body)
             `(PInstall ,pop ,(walk handler active) ,(walk body active))]
            [`(PRuntime ,runtime ,arguments ...)
             `(PRuntime ,runtime ,@(map (lambda (arg) (walk arg active)) arguments))]
            [`(PScopeExit ,places ,body) `(PScopeExit ,places ,(walk body active))]
            [`(PError ,place) `(PError ,place)]
            [`(PResource ,number) `(PResource ,number)]
            [`(PPlace ,place) `(PPlace ,place)]
            [(? symbol? name) (replace-variable name active)]
            [(or (? exact-integer?) (? string?)) term]
            [other (error 'pr-subst* "不正な PR 項: ~s" other)]))
        (walk pc mappings))))

(struct alpha-name (index) #:transparent)

(define (pr-alpha-equivalent? left right)
  (if (not (and (redex-match? PR pc left) (redex-match? PR pc right)))
      (equal? left right)
      (let ()
        (define (normalize pc)
          (define next-index 0)
          (define (fresh)
            (define marker (alpha-name next-index))
            (set! next-index (add1 next-index))
            marker)
          (define (lookup name env)
            (if (pr-variable? name)
                (let ([entry (assq name env)]) (if entry (cdr entry) name))
                name))
          (define (extend names env)
            (for/fold ([markers '()] [env* env]) ([name (in-list names)])
              (define marker (fresh))
              (values (append markers (list marker)) (cons (cons name marker) env*))))
          (define (normalize-branch branch env)
            (match branch
              [`(,constructor (,names ...) -> ,body)
               (define-values (markers env*) (extend names env))
               `(,constructor ,markers -> ,(walk body env*))]))
          (define (walk term env)
            (match term
              [`(PLam (,parameters ...) ,body)
               (define-values (markers env*) (extend parameters env))
               `(PLam ,markers ,(walk body env*))]
              [`(PClosure ((,keys ,values) ...) (,parameters ...) ,body)
               (define-values (markers env*) (extend (append keys parameters) env))
               (define key-count (length keys))
               `(PClosure ,(for/list ([key (in-list (take markers key-count))]
                                      [value (in-list values)])
                             (list key (walk value env)))
                          ,(drop markers key-count)
                          ,(walk body env*))]
              [`(PLet ,name ,bound ,body)
               (define-values (markers env*) (extend (list name) env))
               `(PLet ,(first markers) ,(walk bound env) ,(walk body env*))]
              [`(PLetOwned ,name ,bound ,body)
               (define-values (markers env*) (extend (list name) env))
               `(PLetOwned ,(first markers) ,(walk bound env) ,(walk body env*))]
              [`(PLetrec ,name ,bound ,body)
               (define-values (markers env*) (extend (list name) env))
               `(PLetrec ,(first markers) ,(walk bound env*) ,(walk body env*))]
              [`(PApp ,callee ,arguments ...)
               `(PApp ,(walk callee env) ,@(map (lambda (arg) (walk arg env)) arguments))]
              [`(PTagged ,tag ,children ...)
               `(PTagged ,tag ,@(map (lambda (child) (walk child env)) children))]
              [`(PRec ((,labels ,values) ...))
               `(PRec ,(for/list ([label (in-list labels)] [value (in-list values)])
                         (list label (walk value env))))]
              [`(PRecRewrite ,input ((,labels ,names ,bodies) ...))
               `(PRecRewrite ,(walk input env)
                             ,(for/list ([label (in-list labels)]
                                         [name (in-list names)]
                                         [body (in-list bodies)])
                                (define-values (markers env*) (extend (list name) env))
                                (list label (first markers) (walk body env*))))]
              [`(PRecRemove ,record ,labels) `(PRecRemove ,(walk record env) ,labels)]
              [`(PProj ,record ,label) `(PProj ,(walk record env) ,label)]
              [`(PProjOpt ,tag-a ,tag-b ,record ,label)
               `(PProjOpt ,tag-a ,tag-b ,(walk record env) ,label)]
              [`(PMatch ,scrutinee (,branches ...))
               `(PMatch ,(walk scrutinee env)
                        ,(map (lambda (branch) (normalize-branch branch env)) branches))]
              [`(PPrim ,name ,arguments ...)
               `(PPrim ,name ,@(map (lambda (arg) (walk arg env)) arguments))]
              [`(PEffect ,pop ,payload) `(PEffect ,pop ,(walk payload env))]
              [`(PInstall ,pop ,handler ,body)
               `(PInstall ,pop ,(walk handler env) ,(walk body env))]
              [`(PRuntime ,runtime ,arguments ...)
               `(PRuntime ,runtime ,@(map (lambda (arg) (walk arg env)) arguments))]
              [`(PScopeExit ,places ,body) `(PScopeExit ,places ,(walk body env))]
              [`(PError ,place) `(PError ,place)]
              [`(PResource ,number) `(PResource ,number)]
              [`(PPlace ,place) `(PPlace ,place)]
              [(? symbol? name) (lookup name env)]
              [(or (? exact-integer?) (? string?)) term]))
          (walk pc '()))
        (equal? (normalize left) (normalize right)))))
