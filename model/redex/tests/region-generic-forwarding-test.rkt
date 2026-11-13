#lang racket

(require rackunit
         racket/match
         "../borrow-oracle.rkt"
         "../driver.rkt"
         "../erase.rkt"
         "../gen.rkt"
         "../machine.rkt"
         "../region.rkt"
         "../typing.rkt")

(define source
  (string-append
   "fn ignore(x: &{a: &Int}) -> Int ! {Own, Partial} { return 11 }\n"
   "fn forward(x: &{a: &Int}) -> Int ! {Own, Partial} { return ignore(x) }\n"
   "0"))

(define (contains-form? tree wanted)
  (or (and (pair? tree) (eq? (car tree) wanted))
      (and (pair? tree) (ormap (lambda (part) (contains-form? part wanted)) tree))))

(define (find-forms tree wanted)
  (cond
    [(and (pair? tree) (eq? (car tree) wanted))
     (cons tree (append-map (lambda (part) (find-forms part wanted)) (cdr tree)))]
    [(pair? tree) (append-map (lambda (part) (find-forms part wanted)) tree)]
    [else '()]))

(define (trace-g2 start)
  (let loop ([current start] [configs (list start)] [fuel 10000])
    (when (zero? fuel)
      (error 'trace-g2 "評価 fuel を使い切った: ~s" current))
    (match (raw-steps-g2/named current)
      ['() configs]
      [(list (list _ next))
       (loop next (append configs (list next)) (sub1 fuel))]
      [steps (error 'trace-g2 "一意な次状態でない: ~s" steps)])))

(test-case "借用署名だけを使う generic forwarding は呼出しを実行せず IR 付き Core を作る"
  (define compiled (compile-source/string 'src source))
  (check-true (compiled? compiled)
              (format "Surface forwarding を compile: ~s" compiled))
  (when (compiled? compiled)
    (define core (compiled-core compiled))
    (define callables (compiled-callables compiled))
    (check-false (borrow-bearing-core? core))
    (check-true (borrow-bearing-program? core callables))
    (check-true (contains-form? (compiled-execution-core compiled) 'RegionApp))
    (define ir (build-region-ir core))
    (define typed (core-type-of/regions core '() callables #:ir ir))
    (check-true (region-typed? typed)
                (format "forwarding Core を region 型付け: ~s" typed))
    (when (region-typed? typed)
      (define start
        (inject-g2m (erase-core (region-execution-core typed))))
      (define configs (trace-g2 start))
      (for ([config (in-list configs)] [index (in-naturals)])
        (define row
          (runtime-row config callables (region-typed-type typed)
                       #:region-ir ir))
        (check-not-false row (format "config ~a runtime-row" index))
        (when row
          (check-true
           (config-ok? config callables (region-typed-type typed) row
                       #:region-ir ir)
           (format "config ~a config-ok?" index))))
      (check-equal?
       (check-borrow-execution start (region-typed-sidecar typed)
                               ir 10000 (make-bcounters))
       'ok
       "forwarding Core の実行 trace は borrow oracle を通る"))))

(test-case "borrow-free adapter も callables の借用署名を見て型付けする"
  (define adapter-source
    (string-append
     "fn callback(p: &Int) -> Int ! {Own, Partial} { return 1 }\n"
     "fn source(x: Owned<Int>) -> Int ! {Own, Partial} { return callback(&x) }\n"
     "let adapted: fn(Owned<Int>) -> Int | Bool ! {Own, Partial} = source\n"
     "0"))
  (define compiled (compile-source/string 'src adapter-source))
  (check-true (compiled? compiled)
              (format "Surface borrow-bearing program with function adapter: ~s"
                      compiled))
  (when (compiled? compiled)
    (define callables (compiled-callables compiled))
    (define adapters (find-forms (compiled-core compiled) 'Curry))
    (check-equal? (length adapters) 1)
    (check-false (borrow-bearing-core? (first adapters)))
    (check-true (borrow-bearing-core? callables))
    (check-true (borrow-bearing-program? (first adapters) callables))))
