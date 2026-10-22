#lang racket

(require rackunit
         racket/match
         "../borrow.rkt"
         "../region.rkt"
         "../typing.rkt")

(define owner-type '(Record ((n Int imm) (owned (Owned Res) imm))))
(define borrowed-record-type
  '(Record ((b (Borrowed Int (RParam %omitted)) imm))))
(define function-type `(NFn (,owner-type) Int () (Own) () User))

(define (typed-body body result-type)
  (define core
    `(Lam User adopt-check (raw)
       (Handle (Return boundary ,result-type)
               (return-value -> return-value)
               (Scope ()
                 (Let (x let ,owner-type) raw ,body)))))
  (define ir (build-region-ir core))
  (type-of/raw (annotate-regions core ir)
               '()
               `((adopt-check (NFn (,owner-type) ,result-type () (Own) () User)))
               '()
               (region-ctx ir '() (hash) (hash))))

(define (typed-scoped-record-escape)
  (define core
    `(Scope (1)
       (Let (r let ,borrowed-record-type)
            (Scope (2)
              (Rec ((b imm (ProjBorrow (Borrow 2) n)))))
            r)))
  (define ir (build-region-ir core))
  (type-of/raw (annotate-regions core ir)
               (list (list 1 owner-type) (list 2 owner-type))
               '()
               '()
               (region-ctx ir '()
                           (hash 1 (region-at ir '())
                                 2 (region-at ir '(0 0)))
                           (hash))))

(define (result-key result)
  (match result
    [`(fail ,key ,_node ,_details ...) key]
    [_ #f]))

(define (result-type result)
  (match result
    [`(ok (,type ,_row)) type]
    [_ #f]))

;; Surface の注釈付き／注釈なしはどちらも #:ty を持つ同じ Core 形になる。
(test-case "借用欄を持つ record let は推論寿命を採る"
  (define result
    (typed-body
     `(Let (r let ,borrowed-record-type)
           (Rec ((b imm (ProjBorrow (Borrow x) n))))
           42)
     'Int))
  (check-false (result-key result))
  (check-equal? (result-type result) function-type))

(test-case "通常の注釈なし let の推論寿命採用を保つ"
  (define result
    (typed-body
     '(Let (r let (Borrowed Int (RParam %omitted)))
           (ProjBorrow (Borrow x) n)
           (Read r))
     'Int))
  (check-false (result-key result))
  (check-equal? (result-type result) function-type))

(test-case "所有者の Scope を越える借用欄付き record を拒否する"
  (define result (typed-scoped-record-escape))
  (check-equal? (result-key result) 'borrow-escapes-owner))
