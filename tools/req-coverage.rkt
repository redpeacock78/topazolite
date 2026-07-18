#lang racket

(require racket/runtime-path)

(provide coverage-errors)

(define heading-rx #px"^### ([A-Z]{3}-[0-9]{3}) *$")
(define state-rx #px"^- \\*\\*状態\\*\\*： *(.+?) *$")
(define spec-id-rx #px"\\[REQ: ([A-Z]{3}-[0-9]{3})\\]")
(define test-id-rx #px"[A-Z]{3}-[0-9]{3}")

(define (registry-definitions path)
  (define definitions '())
  (define current-id #f)
  (for ([line (in-list (file->lines path))])
    (match (regexp-match heading-rx line)
      [(list _ id)
       (set! current-id id)
       (set! definitions (cons (cons id #f) definitions))]
      [_
       (when current-id
         (match (regexp-match state-rx line)
           [(list _ state)
            (set! definitions
                  (cons (cons current-id (string-trim state))
                        (cdr definitions)))]
           [_ (void)]))]))
  (reverse definitions))

(define (spec-ids paths)
  (append-map
   (lambda (path)
     (regexp-match* spec-id-rx (file->string path)
                    #:match-select cadr))
   paths))

(define (test-ids paths)
  (append-map
   (lambda (path)
     (regexp-match* test-id-rx (file->string path)))
   paths))

(define (sorted-ids ids)
  (sort (set->list ids) string<?))

(define (coverage-errors registry-path spec-paths test-paths)
  (define definitions (registry-definitions registry-path))
  (define counts (make-hash))
  (for ([definition (in-list definitions)])
    (hash-update! counts (car definition) add1 0))
  (define known (list->set (map car definitions)))
  (define g1
    (list->set
     (for/list ([definition (in-list definitions)]
                #:when (equal? (cdr definition) "G1"))
       (car definition))))
  (define specs (list->set (spec-ids spec-paths)))
  (define tests (list->set (test-ids test-paths)))
  (define duplicates
    (sort
     (for/list ([(id count) (in-hash counts)] #:when (> count 1)) id)
     string<?))
  (append
   (for/list ([id (in-list duplicates)])
     (format "duplicate requirement ID: ~a" id))
   (for/list ([id (in-list
                   (sorted-ids
                    (set-subtract (set-union specs tests) known)))])
     (format "unknown requirement ID: ~a" id))
   (for/list ([id (in-list (sorted-ids (set-subtract g1 specs)))])
     (format "G1 requirement lacks spec annotation: ~a" id))
   (for/list ([id (in-list (sorted-ids (set-subtract g1 tests)))])
     (format "G1 requirement lacks test reference: ~a" id))))

(define-runtime-path tools-directory ".")

(define (matching-files directory extension-rx)
  (sort
   (for/list ([path (in-list (directory-list directory #:build? #t))]
              #:when (regexp-match? extension-rx (path->string path)))
     path)
   string<?
   #:key path->string))

(module+ main
  (define root (simplify-path (build-path tools-directory 'up)))
  (define registry (build-path root "docs/specification/requirements.md"))
  (define specs
    (matching-files (build-path root "docs/specification") #rx"[.]md$"))
  (define tests
    (matching-files (build-path root "model/redex/tests") #rx"[.]rkt$"))
  (define errors (coverage-errors registry specs tests))
  (cond
    [(null? errors)
     (define g1-count
       (set-count
        (list->set
         (for/list ([definition (in-list (registry-definitions registry))]
                    #:when (equal? (cdr definition) "G1"))
           (car definition)))))
     (printf "Requirement coverage OK: ~a G1 IDs\n" g1-count)]
    [else
     (for ([message (in-list errors)])
       (eprintf "~a\n" message))
     (exit 1)]))
