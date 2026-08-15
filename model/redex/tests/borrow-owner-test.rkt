#lang racket

(require rackunit
         racket/set
         "../region.rkt")

;; 手組みの ir。region.md §5 のとおり、手組みの ir は実装誤りを示す
;; fixture のためのものである。
(define ρa (region 100))
(define ρb (region 101))
(define ρroot (region 102))

;; region-owning は gen:region-solver の method であるため、素の region-ir では
;; 呼べない。手組みの fixture も lexical adapter として組む。
;; parents は 2 つの子を root へ結び、at-table は空、points は根だけである。
;; region-at と regions-exiting-at をこの fixture で呼ばないため、この 2 つで足りる。
(define (hand-ir owners)
  (lexical-region-ir (list->set (list ρroot ρa ρb))
                     (list->set (list (list ρroot ρa) (list ρroot ρb)))
                     owners
                     (hash ρa ρroot ρb ρroot)
                     (hash)
                     (set '())))

;; 一意に定まるとき、その region を返す。
(check-equal? (region-owning (hand-ir (hash ρroot '() ρa '(0 1) ρb '(2)))
                             0)
              ρa)

;; 所有者が無いときは error。root region へ落とさない。
;; root は最も長生きするため、黙って root にすると BOR-001 の判定が
;; すべて通ってしまう。
(check-exn exn:fail?
           (lambda ()
             (region-owning (hand-ir (hash ρroot '() ρa '(0) ρb '(1))) 9)))

;; 所有者が 2 つ以上ある IR は不正であり error。
(check-exn exn:fail?
           (lambda ()
             (region-owning (hand-ir (hash ρroot '() ρa '(0) ρb '(0))) 0)))
