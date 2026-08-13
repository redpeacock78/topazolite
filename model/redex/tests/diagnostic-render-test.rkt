#lang racket

(require rackunit
         json
         "../diagnostic.rkt"
         "../diagnostic-render.rkt"
         "../source-map.rkt")

;; spec §13 の fixture 8 件。すべて make-diagnostic で手作りしている。
;; Phase 0 の producer は secondary-labels、notes、help、related を生成しない
;; ため、production 経路から取れない。手作りであることをここへ明記し、
;; production の被覆を偽装しない。
(define fixture-source-id 'sample)

;; 20 byte、2 行。offset 9 と 19 が改行、offset 20 が末尾である。
(define fixture-source "let x = 1\nlet y = 2\n")

(define fixture-source-map
  (make-source-map (hasheq fixture-source-id fixture-source)))

(define s-let '(#:span sample 0 3))
(define s-x '(#:span sample 4 5))
(define s-y '(#:span sample 14 15))
(define s-line2 '(#:span sample 10 19))
(define s-all '(#:span sample 0 20))
(define s-end '(#:span sample 20 20))
(define s-syn '(#:span #:synthetic 0 0))

(define fixture-minimal
  (make-diagnostic #:id "E-VAR-002"
                   #:title "束縛されていない変数である"
                   #:message "束縛されていない変数である"
                   #:primary-span s-x
                   #:source-chain (list (list 'surface 'verbatim s-x))))

(define fixture-synthetic
  (make-diagnostic #:id "E-TYP-002"
                   #:title "期待型なしでは型を合成できない"
                   #:message "期待型なしでは型を合成できない"
                   #:primary-span s-syn
                   #:source-chain (list (list 'surface 'synthetic-span s-syn))))

(define fixture-expected-found
  (make-diagnostic #:id "E-TYP-012"
                   #:title "型が期待と一致しない"
                   #:message "型が期待と一致しない"
                   #:primary-span s-let
                   #:expected 'Bool
                   #:found 'Int
                   #:source-chain (list (list 'surface 'verbatim s-let))))

;; message が title と異なり、かつ複数行である。primary span も複数行にまたがる。
(define fixture-multiline
  (make-diagnostic #:id "E-ARI-001"
                   #:title "与えた式の個数が期待と一致しない"
                   #:message "与えた式の個数が期待と一致しない\n仮引数は 2 個である"
                   #:primary-span s-all
                   #:source-chain (list (list 'surface 'verbatim s-all))))

(define fixture-related
  (make-diagnostic #:id "E-VAR-001"
                   #:title "仮引数名が重複している"
                   #:message "仮引数名が重複している"
                   #:primary-span s-x
                   #:related (list (list 'defined-here s-y "先に束縛した位置")
                                   (list 'introduced-by s-syn "展開が導入した束縛"))
                   #:source-chain (list (list 'surface 'verbatim s-x))))

(define fixture-secondary
  (make-diagnostic #:id "E-DAT-004"
                   #:title "Eliminate が構築子を尽くしていない"
                   #:message "Eliminate が構築子を尽くしていない"
                   #:primary-span s-let
                   #:secondary-labels (list (list s-y "この構築子が漏れている")
                                            (list s-syn "既定の分岐は無い"))
                   #:notes (list "構築子は 2 個ある")
                   #:help (list "残る構築子の分岐を足す")
                   #:source-chain (list (list 'surface 'verbatim s-let))))

;; capability-diagnostic の reason は文字列で found へ入る。
;; §11 が ~s を要求する理由をここでも踏む。
(define fixture-lowering
  (make-diagnostic #:id "E-LOW-001"
                   #:title "Typed Core の kernel primitive は写し先を持たない"
                   #:message "Typed Core の kernel primitive は写し先を持たない"
                   #:primary-span s-line2
                   #:found "kernel primitive には写し先が無い"
                   #:backend 'racket-cs
                   #:source-chain (list (list 'surface 'verbatim s-line2))))

;; 2 つの frame の phase と kind と span がすべて異なる。
;; chain の全要素を先頭 frame の値で埋める実装を落とすためである。
;; effect-context と proof-context はどちらも記号と文字列を含む。
(define fixture-chain
  (make-diagnostic #:id "E-EFF-002"
                   #:title "関数が宣言していない効果を残す"
                   #:message "関数が宣言していない効果を残す"
                   #:primary-span s-end
                   #:effect-context '(Yield Int "handler が無い")
                   #:proof-context '(Prop positive "義務が残る")
                   #:source-chain (list (list 'surface 'verbatim s-x)
                                        (list 'elaborate 'synthesized s-y))))

(define fixture-table
  (list (list 'minimal fixture-minimal)
        (list 'synthetic fixture-synthetic)
        (list 'expected-found fixture-expected-found)
        (list 'multiline fixture-multiline)
        (list 'related fixture-related)
        (list 'secondary fixture-secondary)
        (list 'lowering fixture-lowering)
        (list 'chain fixture-chain)))

(define (fixture name)
  (cond
    [(assq name fixture-table) => second]
    [else (error 'fixture "無い fixture である: ~s" name)]))

;; 位置を持つ 3 欄の span をすべて集める。fixture が source-map で引ける span
;; だけを持つことを確かめるために使う。
(define (fixture-spans d)
  (append (list (diagnostic-primary-span d))
          (map first (diagnostic-secondary-labels d))
          (map second (diagnostic-related d))))

(test-case
 "fixture 8 件はすべて schema を満たす"
 (check-equal? (length fixture-table) 8)
 (for ([row (in-list fixture-table)])
   (match-define (list name d) row)
   (check-equal? (diagnostic-schema-errors d) '() (format "~a" name))
   (check-true (diagnostic-valid? d) (format "~a" name))))

;; renderer より前に、fixture の span がすべて位置へ変換できることを固定する。
;; ここが通らない fixture を置くと、Task 3 以降の失敗が renderer の誤りなのか
;; fixture の誤りなのか読み取れなくなる。
(test-case
 "fixture の位置欄はすべて span->location を通る"
 (for ([row (in-list fixture-table)])
   (match-define (list name d) row)
   (for ([span (in-list (fixture-spans d))])
     (check-pred location?
                 (span->location fixture-source-map span)
                 (format "~a ~s" name span)))))

(test-case
 "fixture 4 の message は title と異なり複数行である"
 (define d (fixture 'multiline))
 (check-not-equal? (diagnostic-message d) (diagnostic-title d))
 (check-equal? (length (string-split (diagnostic-message d) "\n" #:trim? #f)) 2)
 ;; primary span は複数行にまたがる。
 (define loc (span->location fixture-source-map (diagnostic-primary-span d)))
 (check-not-equal? (location-start-line loc) (location-end-line loc)))

(test-case
 "fixture 5 と 6 は位置欄に synthetic を 1 件だけ混ぜる"
 (define related (diagnostic-related (fixture 'related)))
 (check-equal? (length related) 2)
 (check-equal? (for/sum ([r (in-list related)])
                 (if (location-synthetic?
                      (span->location fixture-source-map (second r)))
                     1 0))
               1)
 (define labels (diagnostic-secondary-labels (fixture 'secondary)))
 (check-equal? (length labels) 2)
 (check-equal? (for/sum ([lab (in-list labels)])
                 (if (location-synthetic?
                      (span->location fixture-source-map (first lab)))
                     1 0))
               1)
 ;; notes と help も同じ fixture が持つ。
 (check-equal? (diagnostic-notes (fixture 'secondary)) (list "構築子は 2 個ある"))
 (check-equal? (diagnostic-help (fixture 'secondary))
               (list "残る構築子の分岐を足す")))

(test-case
 "fixture 7 は backend を持ち found が文字列である"
 (define d (fixture 'lowering))
 (check-equal? (diagnostic-backend d) 'racket-cs)
 (check-pred string? (diagnostic-found d))
 ;; 他の 7 件は backend を持たない。
 (for ([row (in-list fixture-table)]
       #:unless (eq? (first row) 'lowering))
   (check-false (diagnostic-backend (second row)) (format "~a" (first row)))))

(test-case
 "fixture 8 の source-chain は 2 frame で 3 欄すべてが異なる"
 (define d (fixture 'chain))
 (define chain (diagnostic-source-chain d))
 (check-equal? (length chain) 2)
 (match-define (list (list phase-1 kind-1 span-1)
                     (list phase-2 kind-2 span-2))
   chain)
 (check-not-equal? phase-1 phase-2)
 (check-not-equal? kind-1 kind-2)
 (check-not-equal? span-1 span-2)
 ;; effect-context と proof-context は記号と文字列の双方を含む。
 (define (has-symbol-and-string? v)
   (and (list? v) (ormap symbol? v) (ormap string? v)))
 (check-true (has-symbol-and-string? (diagnostic-effect-context d)))
 (check-true (has-symbol-and-string? (diagnostic-proof-context d))))

;; spec §11: 整形は ~s であり、文字列は引用符付きで現れる。
;; ~a で写す実装は引用符を落とすため、第 2 行と第 3 行で落ちる。
(test-case
 "format-unfixed は ~s の綴りを出す"
 (check-equal? (format-unfixed 'Bool) "Bool")
 (check-equal? (format-unfixed "reason") "\"reason\"")
 (check-equal? (format-unfixed '(Yield Int "handler が無い"))
               "(Yield Int \"handler が無い\")")
 (check-equal? (format-unfixed '()) "()"))

;; spec §11: #f は JSON の null へ写し、他の値は ~s の文字列へ写す。
(test-case
 "unfixed->jsexpr は #f を json-null へ写す"
 (check-equal? (unfixed->jsexpr #f) (json-null))
 (check-equal? (unfixed->jsexpr 'Bool) "Bool")
 (check-true (jsexpr? (unfixed->jsexpr #f)))
 (check-true (jsexpr? (unfixed->jsexpr '(Prop positive "義務が残る")))))

;; spec §18: sourceId から URI への変換の 6 行。
;; #:synthetic と記号 synthetic が衝突しないことを同じ表で固定する。
(define uri-table
  (list
   (list '#:synthetic "topazolite:%23%3Asynthetic")
   (list 'synthetic "topazolite:synthetic")
   (list (string->symbol "a#b") "topazolite:a%23b")
   (list (string->symbol "a:b") "topazolite:a%3Ab")
   (list (string->symbol "a b") "topazolite:a%20b")
   (list (string->symbol "a😀") "topazolite:a%F0%9F%98%80")))

(test-case
 "source-id->uri は unreserved 以外を percent-encoding する"
 (for ([row (in-list uri-table)])
   (match-define (list sid expected) row)
   (check-equal? (source-id->uri sid) expected (format "~s" sid))))

(test-case
 "span->jsexpr は sourceId を綴りへ写し synthetic を真偽値で出す"
 (check-equal? (span->jsexpr s-x)
               (hasheq 'sourceId "sample" 'startByte 4 'endByte 5
                       'synthetic #f))
 (check-equal? (span->jsexpr s-syn)
               (hasheq 'sourceId "#:synthetic" 'startByte 0 'endByte 0
                       'synthetic #t))
 (check-true (jsexpr? (span->jsexpr s-syn))))
