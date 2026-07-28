#lang racket
(require rackunit racket/match "../elaborate.rkt")

;; elab は 1 引数で、成功時に (list core type row callables) を返す。
;; 失敗時は (err reason)。elaborate-record-test.rkt の規約に合わせる。
(define (elab-type term) (match (elab term) [(list _ type _ _) type]))
(define (elab-error? term) (match (elab term) [`(err ,_) #t] [_ #f]))

;; RFN-001: 導入 primitive を表層から呼べる。
(check-equal? (elab-type '(Apply untrustedInt 8080)) '(Untrusted Int))
(check-equal? (elab-type '(Apply untrustedString "localhost"))
              '(Untrusted String))

;; RFN-001: validate の返り値は Result で、ok 側が Refined である。
(check-equal? (elab-type '(Apply validPort (Apply untrustedInt 8080)))
              '(Result (Refined Int (Prop ValidPort)) String))
(check-equal? (elab-type '(Apply nonEmpty (Apply untrustedString "a")))
              '(Result (Refined String (Prop NonEmpty)) String))

;; RFN-001: Untrusted を型注釈に書ける。
(check-equal? (elab-type '(Fn ((x (Untrusted Int))) (Untrusted Int) () x))
              '(NFn ((Untrusted Int)) (Untrusted Int) () ()))
(check-equal?
 (elab-type '(Fn ((x (Refined Int (Prop ValidPort)))) Int () 1))
 '(NFn ((Refined Int (Prop ValidPort))) Int () ()))

;; RFN-001: 判定表に無い命題は注釈に書けない。
(check-true (elab-error? '(Fn ((x (Refined Int (Prop ValidHost)))) Int () 1)))
(check-true (elab-error? '(Fn ((x (Proof (Prop ValidHost)))) Int () 1)))

;; RFN-002: 常在性 witness は表層に書けない。merge の局所検査だけで立つ命題で
;; あり、利用者が注釈として書く対象ではない。
(check-true (elab-error? '(Fn ((x (Refined Int (Presence a)))) Int () 1)))
(check-true (elab-error? '(Fn ((x (Proof (Presence a)))) Int () 1)))
(check-true
 (elab-error? '(Fn ((f (NFn (Int) Int () ((Presence a))))) Int () 1)))

;; RFN-001: obligation には判定表の命題を書ける。
(check-false
 (elab-error? '(Fn ((f (NFn (Int) Int () ((Prop ValidPort))))) Int () 1)))
(check-true
 (elab-error? '(Fn ((f (NFn (Int) Int () ((Prop ValidHost))))) Int () 1)))

;; RFN-001: Owned を部分に含むペイロードは注釈でも拒否する。
(check-true (elab-error? '(Fn ((x (Untrusted (Owned Res)))) Int () 1)))
(check-true (elab-error? '(Fn ((x (Untrusted (List (Owned Res))))) Int () 1)))
(check-true
 (elab-error? '(Fn ((x (Refined (Owned Res) (Prop ValidPort)))) Int () 1)))

;; G1 の命題は従来どおり書ける。
(check-false (elab-error? '(Fn ((x (Proof TypeNarrativeCap))) Int () 1)))
