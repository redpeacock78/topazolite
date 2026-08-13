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

;; spec §8: terminal は plain text であり ANSI escape を含まない。
;; 8 件の fixture のうち 6 件は出力の全文を固定する。
;; 行の並び（header、位置行、抜粋、caret、secondary の位置行、= の補足行）を
;; 部分一致で確かめると、行の順序を入れ替えた実装が通ってしまう。

(test-case
 "minimal の terminal 出力の全文"
 (check-equal?
  (render-terminal (fixture 'minimal) fixture-source-map)
  (string-join
   (list "error[E-VAR-002]: 束縛されていない変数である"
         "  --> sample:1:5"
         "let x = 1"
         "    ^")
   "\n")))

;; spec §7: synthetic は source を持たないため、抜粋と caret 行を出さない。
;; 位置欄は 1:1 ではなく <synthetic> である。
(test-case
 "synthetic の terminal 出力は位置行を marker にし抜粋を出さない"
 (check-equal?
  (render-terminal (fixture 'synthetic) fixture-source-map)
  (string-join
   (list "error[E-TYP-002]: 期待型なしでは型を合成できない"
         "  --> <synthetic>")
   "\n")))

(test-case
 "expected と found の 2 行が第 2 行と第 3 行の順で出る"
 (check-equal?
  (render-terminal (fixture 'expected-found) fixture-source-map)
  (string-join
   (list "error[E-TYP-012]: 型が期待と一致しない"
         "  --> sample:1:1"
         "let x = 1"
         "^^^"
         "  = expected: Bool"
         "  = found: Int")
   "\n")))

;; spec §8: primary span が複数行にまたがるときは開始行だけを出し、caret は
;; 開始列から行末までとする。
;; message が title と異なるので、第 1 行が message の 2 行として出る。
(test-case
 "複数行 span の caret は開始行の行末で止まる"
 (check-equal?
  (render-terminal (fixture 'multiline) fixture-source-map)
  (string-join
   (list "error[E-ARI-001]: 与えた式の個数が期待と一致しない"
         "  --> sample:1:1"
         "let x = 1"
         "^^^^^^^^^"
         "  = 与えた式の個数が期待と一致しない"
         "  = 仮引数は 2 個である")
   "\n")))

;; caret の空白と幅は location と同じ UTF-16 code unit で数える。
(test-case
 "多 byte 文字を含む source の caret は UTF-16 code unit で揃う"
 (define source-map (make-source-map (hasheq 'wide "あb")))
 (define span '(#:span wide 3 4))
 (define d
   (make-diagnostic #:id "E-VAR-002"
                    #:title "束縛されていない変数である"
                    #:message "束縛されていない変数である"
                    #:primary-span span
                    #:source-chain (list (list 'surface 'verbatim span))))
 (check-equal?
  (render-terminal d source-map)
  (string-join
   (list "error[E-VAR-002]: 束縛されていない変数である"
         "  --> wide:1:2"
         "あb"
         " ^")
   "\n")))

;; spec §8 第 8 行と §7: related の位置欄は synthetic のとき <synthetic> になる。
;; relation を落とさないことも同じ行で固定する。
(test-case
 "related は relation と位置と description を 1 行へ並べる"
 (check-equal?
  (render-terminal (fixture 'related) fixture-source-map)
  (string-join
   (list "error[E-VAR-001]: 仮引数名が重複している"
         "  --> sample:1:5"
         "let x = 1"
         "    ^"
         "  = related[defined-here] sample:2:5: 先に束縛した位置"
         "  = related[introduced-by] <synthetic>: 展開が導入した束縛")
   "\n")))

;; spec §8 の並び 4 と 5: secondary の位置行は = の補足行より前に出る。
;; spec §12: note と help は接頭辞で区別する。
(test-case
 "secondary の位置行は補足行より前に出て note と help が続く"
 (check-equal?
  (render-terminal (fixture 'secondary) fixture-source-map)
  (string-join
   (list "error[E-DAT-004]: Eliminate が構築子を尽くしていない"
         "  --> sample:1:1"
         "let x = 1"
         "^^^"
         "  --> sample:2:5: この構築子が漏れている"
         "  --> <synthetic>: 既定の分岐は無い"
         "  = note: 構築子は 2 個ある"
         "  = help: 残る構築子の分岐を足す")
   "\n")))

;; spec §11: found の文字列は ~s なので引用符が付く。
;; spec §8 第 9 行: backend は補足行の最後である。
(test-case
 "found の文字列は引用符付きで出て backend が最後の行になる"
 (check-equal?
  (render-terminal (fixture 'lowering) fixture-source-map)
  (string-join
   (list "error[E-LOW-001]: Typed Core の kernel primitive は写し先を持たない"
         "  --> sample:2:1"
         "let y = 2"
         "^^^^^^^^^"
         "  = found: \"kernel primitive には写し先が無い\""
         "  = backend: racket-cs")
   "\n")))

;; 空 span の caret は 1 文字分である。
;; source の末尾の offset 20 は 3 行目の先頭であり、その行は空文字列である。
;; 抜粋の行が空でも caret 行は出す。出さない実装は行数が 1 つ足りなくなる。
(test-case
 "空 span の caret は 1 文字分で effect と proof が続く"
 (check-equal?
  (render-terminal (fixture 'chain) fixture-source-map)
  (string-join
   (list "error[E-EFF-002]: 関数が宣言していない効果を残す"
         "  --> sample:3:1"
         ""
         "^"
         "  = effect: (Yield Int \"handler が無い\")"
         "  = proof: (Prop positive \"義務が残る\")")
   "\n")))

;; severity は語をそのまま使う。3 つの語が header の先頭へ出ることを固定する。
(test-case
 "severity の 3 語は header へそのまま出る"
 (for ([sev (in-list '(error warning note))])
   (define d
     (make-diagnostic #:id "E-VAR-002"
                      #:severity sev
                      #:title "束縛されていない変数である"
                      #:message "束縛されていない変数である"
                      #:primary-span s-x
                      #:source-chain (list (list 'surface 'verbatim s-x))))
   (check-equal? (first (string-split (render-terminal d fixture-source-map)
                                      "\n" #:trim? #f))
                 (format "~a[E-VAR-002]: 束縛されていない変数である" sev))))

;; 出力は ANSI escape を含まない。色は Phase 2 以降の Rust renderer が持つ。
(test-case
 "terminal の出力に ANSI escape が無い"
 (for ([row (in-list fixture-table)])
   (match-define (list name d) row)
   (check-false (regexp-match? #rx"\033" (render-terminal d fixture-source-map))
                (format "~a" name))))

;; spec §9: 返り値は client へ JSON として送られる。
;; data へ記号が残ると返り値全体が jsexpr? を満たさなくなるため、8 件すべてで
;; 確かめる。1 件だけで確かめると、特定の欄にだけ記号が残る実装を見逃す。
(test-case
 "LSP の返り値は 8 件すべてで jsexpr? を満たす"
 (for ([row (in-list fixture-table)])
   (match-define (list name d) row)
   (define j (render-lsp d fixture-source-map))
   (check-true (jsexpr? j) (format "~a" name))
   ;; data を単体でも通す。返り値全体だけを見ると、原因が data の中にあるのか
   ;; 最上位の欄にあるのかが失敗の出力から読み取れない（spec §18）。
   (check-true (jsexpr? (hash-ref j 'data)) (format "~a の data" name))))

(test-case
 "LSP の最上位は 7 key で source が固定文字列である"
 (define j (render-lsp (fixture 'minimal) fixture-source-map))
 (check-equal? (list->seteq (hash-keys j))
               (seteq 'range 'severity 'code 'source 'message
                      'relatedInformation 'data))
 (check-equal? (hash-ref j 'code) "E-VAR-002")
 (check-equal? (hash-ref j 'source) "topazolite")
 ;; range は 0 起点である。terminal の 1:5 と同じ位置を指す。
 (check-equal? (hash-ref j 'range)
               (hasheq 'start (hasheq 'line 0 'character 4)
                       'end (hasheq 'line 0 'character 5)))
 ;; message が title と同じときは title の 1 行だけである。
 (check-equal? (hash-ref j 'message) "束縛されていない変数である")
 (check-equal? (hash-ref j 'relatedInformation) '()))

;; spec §9: top level の uri は置かない。uri は publishDiagnostics の params が
;; 持ち、Diagnostic 自体は持たない。
(test-case
 "LSP の最上位に uri を置かない"
 (for ([row (in-list fixture-table)])
   (match-define (list name d) row)
   (check-false (hash-has-key? (render-lsp d fixture-source-map) 'uri)
                (format "~a" name))))

(test-case
 "severity は error が 1、warning が 2、note が 3 である"
 (for ([pair (in-list '((error 1) (warning 2) (note 3)))])
   (match-define (list sev expected) pair)
   (define d
     (make-diagnostic #:id "E-VAR-002"
                      #:severity sev
                      #:title "束縛されていない変数である"
                      #:message "束縛されていない変数である"
                      #:primary-span s-x
                      #:source-chain (list (list 'surface 'verbatim s-x))))
   (check-equal? (hash-ref (render-lsp d fixture-source-map) 'severity)
                 expected
                 (format "~a" sev))))

;; spec §9: message は title の行を先頭に置き、そのあとへ §8 の第 1 行から
;; 第 7 行を = の接頭辞なしで並べる。
;; multiline は message が title と異なるため、title の行に続いて message の
;; 2 行が出る。先頭 2 行が同じ文になるのは、fixture の message の第 1 行が
;; title と同じ文だからである。
(test-case
 "LSP の message は title の行に補足行を接頭辞なしで続ける"
 (check-equal? (hash-ref (render-lsp (fixture 'multiline) fixture-source-map)
                         'message)
               (string-join
                (list "与えた式の個数が期待と一致しない"
                      "与えた式の個数が期待と一致しない"
                      "仮引数は 2 個である")
                "\n"))
 (check-equal? (hash-ref (render-lsp (fixture 'secondary) fixture-source-map)
                         'message)
               (string-join
                (list "Eliminate が構築子を尽くしていない"
                      "note: 構築子は 2 個ある"
                      "help: 残る構築子の分岐を足す")
                "\n"))
 ;; 位置は range と relatedInformation が持つので message へは入れない。
 ;; backend は §8 第 9 行であり、第 1 行から第 7 行の外なので message へ出ない。
 (define lowering-message
   (hash-ref (render-lsp (fixture 'lowering) fixture-source-map) 'message))
 (check-false (regexp-match? #rx"backend" lowering-message))
 (check-false (regexp-match? #rx"-->" lowering-message)))

;; spec §7 と §9: synthetic の range は空だが、それだけでは source の先頭を指す
;; 実在の位置と区別できない。data の synthetic が真であることが marker である。
(test-case
 "synthetic の range は空で data の synthetic が真である"
 (define j (render-lsp (fixture 'synthetic) fixture-source-map))
 (check-equal? (hash-ref j 'range)
               (hasheq 'start (hasheq 'line 0 'character 0)
                       'end (hasheq 'line 0 'character 0)))
 (check-true (hash-ref (hash-ref j 'data) 'synthetic))
 (check-equal? (hash-ref (hash-ref j 'data) 'sourceId) "#:synthetic")
 ;; 実在の source を持つ診断は偽である。
 (check-false (hash-ref (hash-ref (render-lsp (fixture 'minimal)
                                              fixture-source-map)
                                  'data)
                        'synthetic)))

;; spec §9: relatedInformation の message は relation を落とさず、synthetic の
;; ときは description の直前へ marker を置く。
(test-case
 "relatedInformation は relation と synthetic marker を message へ載せる"
 (define j (render-lsp (fixture 'related) fixture-source-map))
 (define infos (hash-ref j 'relatedInformation))
 (check-equal? (length infos) 2)
 (check-equal? (first infos)
               (hasheq 'location
                       (hasheq 'uri "topazolite:sample"
                               'range (hasheq 'start (hasheq 'line 1 'character 4)
                                              'end (hasheq 'line 1 'character 5)))
                       'message "[defined-here] 先に束縛した位置"))
 (check-equal? (second infos)
               (hasheq 'location
                       (hasheq 'uri "topazolite:%23%3Asynthetic"
                               'range (hasheq 'start (hasheq 'line 0 'character 0)
                                              'end (hasheq 'line 0 'character 0)))
                       'message "[introduced-by] <synthetic> 展開が導入した束縛")))

;; spec §12: secondary-labels は relatedInformation へ混ぜず data へ置く。
;; 混ぜる実装は relatedInformation の件数が 2 になり、ここで落ちる。
(test-case
 "secondary-labels は data へ入り relatedInformation へ混ざらない"
 (define j (render-lsp (fixture 'secondary) fixture-source-map))
 (check-equal? (hash-ref j 'relatedInformation) '())
 (check-equal? (hash-ref (hash-ref j 'data) 'secondaryLabels)
               (list (hasheq 'range (hasheq 'start (hasheq 'line 1 'character 4)
                                            'end (hasheq 'line 1 'character 5))
                             'message "この構築子が漏れている"
                             'sourceId "sample"
                             'synthetic #f)
                     (hasheq 'range (hasheq 'start (hasheq 'line 0 'character 0)
                                            'end (hasheq 'line 0 'character 0))
                             'message "既定の分岐は無い"
                             'sourceId "#:synthetic"
                             'synthetic #t))))

;; spec §9 の data の値域。記号を残さず文字列と json-null へ写す。
(test-case
 "data の backend は記号を文字列へ写し #f を json-null へ写す"
 (define lowering-data
   (hash-ref (render-lsp (fixture 'lowering) fixture-source-map) 'data))
 (check-equal? (hash-ref lowering-data 'backend) "racket-cs")
 (check-equal? (hash-ref lowering-data 'found)
               "\"kernel primitive には写し先が無い\"")
 (for ([row (in-list fixture-table)]
       #:unless (eq? (first row) 'lowering))
   (check-equal? (hash-ref (hash-ref (render-lsp (second row)
                                                 fixture-source-map)
                                     'data)
                           'backend)
                 (json-null)
                 (format "~a" (first row)))))

;; spec §9: sourceChain を落とすと DIA-003 の provenance が LSP でだけ機械可読で
;; なくなる。effectContext と proofContext も同じ理由で置く。
(test-case
 "data は sourceChain と effectContext と proofContext を持つ"
 (define data (hash-ref (render-lsp (fixture 'chain) fixture-source-map) 'data))
 (check-equal? (list->seteq (hash-keys data))
               (seteq 'synthetic 'sourceId 'startByte 'endByte 'category
                      'schemaVersion 'backend 'expected 'found
                      'secondaryLabels 'sourceChain
                      'effectContext 'proofContext))
 (check-equal? (hash-ref data 'category) "EFF")
 (check-equal? (hash-ref data 'schemaVersion) diagnostic-schema-version)
 (check-equal? (hash-ref data 'startByte) 20)
 (check-equal? (hash-ref data 'endByte) 20)
 (check-equal? (hash-ref data 'sourceChain)
               (list (hasheq 'phase "surface" 'kind "verbatim"
                             'span (hasheq 'sourceId "sample" 'startByte 4
                                           'endByte 5 'synthetic #f))
                     (hasheq 'phase "elaborate" 'kind "synthesized"
                             'span (hasheq 'sourceId "sample" 'startByte 14
                                           'endByte 15 'synthetic #f))))
 (check-equal? (hash-ref data 'effectContext) "(Yield Int \"handler が無い\")")
 (check-equal? (hash-ref data 'proofContext) "(Prop positive \"義務が残る\")")
 (check-equal? (hash-ref data 'expected) (json-null)))

;; spec §10: Diagnostic の 18 欄をすべて写し、schemaVersion と registryVersion を
;; 最上位へ置く。合計 20 key である。
;; 件数だけでなく key の集合で確かめる。件数だけだと、欄を 1 つ落として別の名前を
;; 足した実装が通ってしまう。
(define json-keys
  (seteq 'id 'severity 'category 'title 'message
         'primarySpan 'secondaryLabels 'notes 'help
         'expected 'found
         'sourceChain 'expansionTrace
         'effectContext 'proofContext
         'related 'fixes 'backend
         'schemaVersion 'registryVersion))

(test-case
 "JSON は 20 key を持ち 8 件すべてで jsexpr? を満たす"
 (for ([row (in-list fixture-table)])
   (match-define (list name d) row)
   (define j (render-json d))
   (check-true (jsexpr? j) (format "~a" name))
   (check-equal? (list->seteq (hash-keys j)) json-keys (format "~a" name))))

;; jsexpr? を満たすことと、実際に書き出して読み戻せることは別である。
;; hasheq の key へ記号でない値が混ざる実装は、この往復で落ちる。
(test-case
 "JSON は書き出して読み戻すと同じ値になる"
 (define j (render-json (fixture 'chain)))
 (check-equal? (string->jsexpr (jsexpr->string j)) j))

(test-case
 "第 1 群の 5 欄は素の値を文字列へ写す"
 (define j (render-json (fixture 'lowering)))
 (check-equal? (hash-ref j 'id) "E-LOW-001")
 (check-equal? (hash-ref j 'severity) "error")
 (check-equal? (hash-ref j 'category) "LOW")
 (check-equal? (hash-ref j 'title) "Typed Core の kernel primitive は写し先を持たない")
 (check-equal? (hash-ref j 'message) "Typed Core の kernel primitive は写し先を持たない")
 (check-equal? (hash-ref j 'backend) "racket-cs")
 (check-equal? (hash-ref (render-json (fixture 'minimal)) 'backend)
               (json-null))
 (check-equal? (hash-ref j 'schemaVersion) diagnostic-schema-version)
 (check-equal? (hash-ref j 'registryVersion) diagnostic-registry-version))

;; spec §10 の第 2 群。要素形が定まる 4 欄を object へ再帰的に写す。
;; 文字列化の既定へ落とすと (surface verbatim (#:span src 0 4)) が 1 個の文字列に
;; なり、受け手が欄を分解できなくなる。
(test-case
 "第 2 群の 4 欄は要素ごとに object へ写す"
 (define j (render-json (fixture 'related)))
 (check-equal? (hash-ref j 'primarySpan)
               (hasheq 'sourceId "sample" 'startByte 4 'endByte 5
                       'synthetic #f))
 (check-equal? (hash-ref j 'related)
               (list (hasheq 'relation "defined-here"
                             'span (hasheq 'sourceId "sample" 'startByte 14
                                           'endByte 15 'synthetic #f)
                             'description "先に束縛した位置")
                     (hasheq 'relation "introduced-by"
                             'span (hasheq 'sourceId "#:synthetic" 'startByte 0
                                           'endByte 0 'synthetic #t)
                             'description "展開が導入した束縛")))
 (define k (render-json (fixture 'secondary)))
 (check-equal? (hash-ref k 'secondaryLabels)
               (list (hasheq 'span (hasheq 'sourceId "sample" 'startByte 14
                                           'endByte 15 'synthetic #f)
                             'label "この構築子が漏れている")
                     (hasheq 'span (hasheq 'sourceId "#:synthetic" 'startByte 0
                                           'endByte 0 'synthetic #t)
                             'label "既定の分岐は無い")))
 ;; notes と help は文字列の list なのでそのまま写す。
 (check-equal? (hash-ref k 'notes) (list "構築子は 2 個ある"))
 (check-equal? (hash-ref k 'help) (list "残る構築子の分岐を足す"))
 (define c (render-json (fixture 'chain)))
 (check-equal? (hash-ref c 'sourceChain)
               (list (hasheq 'phase "surface" 'kind "verbatim"
                             'span (hasheq 'sourceId "sample" 'startByte 4
                                           'endByte 5 'synthetic #f))
                     (hasheq 'phase "elaborate" 'kind "synthesized"
                             'span (hasheq 'sourceId "sample" 'startByte 14
                                           'endByte 15 'synthetic #f)))))

;; spec §10 の第 3 群。形を固定しない 4 欄は §11 の整形を通した文字列であり、
;; #f のときは json-null である。
(test-case
 "第 3 群の 4 欄は整形した文字列か json-null である"
 (define j (render-json (fixture 'expected-found)))
 (check-equal? (hash-ref j 'expected) "Bool")
 (check-equal? (hash-ref j 'found) "Int")
 (check-equal? (hash-ref j 'effectContext) (json-null))
 (check-equal? (hash-ref j 'proofContext) (json-null))
 (define c (render-json (fixture 'chain)))
 (check-equal? (hash-ref c 'effectContext) "(Yield Int \"handler が無い\")")
 (check-equal? (hash-ref c 'proofContext) "(Prop positive \"義務が残る\")")
 ;; found の文字列は ~s なので引用符が残る。~a にすると記号と区別が付かない。
 (check-equal? (hash-ref (render-json (fixture 'lowering)) 'found)
               "\"kernel primitive には写し先が無い\""))

;; schema version 3 は expansion-trace と fixes へ空を要求する。
(test-case
 "expansionTrace と fixes は空の list である"
 (for ([row (in-list fixture-table)])
   (match-define (list name d) row)
   (define j (render-json d))
   (check-equal? (hash-ref j 'expansionTrace) '() (format "~a" name))
   (check-equal? (hash-ref j 'fixes) '() (format "~a" name))))

;; spec §9 と §10: sourceId の綴りは 2 つの形式で同じである。
;; 別の綴りにすると parity の外側にある欄で形式ごとの差が生まれる。
(test-case
 "sourceId の綴りは JSON と LSP の data で一致する"
 (for ([row (in-list fixture-table)])
   (match-define (list name d) row)
   (check-equal? (hash-ref (hash-ref (render-json d) 'primarySpan) 'sourceId)
                 (hash-ref (hash-ref (render-lsp d fixture-source-map) 'data)
                           'sourceId)
                 (format "~a" name))))

;; ---- parity（spec §13）------------------------------------------------
;; [REQ: DIA-004] terminal、LSP、JSON の 3 形式は同一の Diagnostic IR を入力と
;; し、10 の観測量で一致する。
;; 3 形式は同じ情報を別の単位と器で書くため、突き合わせる前に共通の形へ
;; 正規化する。取り出しは renderer の内部を呼ばずにこの節で書き下ろす。
;; renderer の関数を借りると、renderer の誤りが取り出しにも同じ形で現れ、
;; 比較で相殺される。

;; 観測する位置。始まりだけを持つ。
;; terminal の位置行は始まりしか出さないため、終わりを入れると契約どおりの
;; 実装でも 3 形式が食い違う。
;; 終わりの意味が失われるわけではない。parity は共通部分だけを見る層であり、
;; 終わりは source-map-test.rkt の location 全体の検査と、形式ごとの
;; output-shape の試験（range、caret、byte offset）が固定する（spec §13）。
(struct ppos (source-id synthetic? line character) #:transparent)

;; 10 の観測量。backend と message は入れない。
(struct parity (code severity title position expected found
                notes help related secondary)
  #:transparent)

;; 欄が無いときの #f と、1 行だけ現れるときの文字列を分ける。
(define (single texts)
  (match texts
    ['() #f]
    [(list one) one]
    [_ (error 'single "1 行に収まらない: ~s" texts)]))

(define (lines-with-prefix lines prefix)
  (for/list ([line (in-list lines)] #:when (string-prefix? line prefix))
    (substring line (string-length prefix))))

;; ---- terminal 側の取り出し --------------------------------------------

;; "sample:2:5" と "<synthetic>" の 2 形を受ける。
;; terminal だけが 1 起点なので、ここで 0 起点へ戻す。
(define (parse-position-text text)
  (cond
    [(string=? text "<synthetic>") (ppos "#:synthetic" #t 0 0)]
    [(regexp-match #px"^(.+):([0-9]+):([0-9]+)$" text)
     => (lambda (m)
          (match-define (list _ spelling line column) m)
          (ppos spelling #f
                (sub1 (string->number line))
                (sub1 (string->number column))))]
    [else (error 'parse-position-text "位置の形ではない: ~s" text)]))

(define header-rx #px"^([a-z]+)\\[([^]]+)\\]: (.*)$")
(define labelled-rx #px"^(<synthetic>|.+?:[0-9]+:[0-9]+): (.*)$")
(define related-rx
  #px"^related\\[([^]]+)\\] (<synthetic>|.+?:[0-9]+:[0-9]+): (.*)$")

(define (terminal-parity s)
  (define lines (string-split s "\n" #:trim? #f))
  (match-define (list _ severity code title)
    (or (regexp-match header-rx (first lines))
        (error 'terminal-parity "見出し行の形ではない: ~s" (first lines))))
  ;; 位置行のうち最初の 1 本が primary であり、残りが secondary-labels である。
  ;; 順序は §8 が固定しているため、行の並びをそのまま順序として読む。
  (define position-texts (lines-with-prefix lines "  --> "))
  (define supplements (lines-with-prefix lines "  = "))
  (parity
   code
   (string->symbol severity)
   title
   (parse-position-text (first position-texts))
   (single (lines-with-prefix supplements "expected: "))
   (single (lines-with-prefix supplements "found: "))
   (lines-with-prefix supplements "note: ")
   (lines-with-prefix supplements "help: ")
   (for/list ([line (in-list supplements)]
              #:when (regexp-match related-rx line))
     (match-define (list _ relation position description)
       (regexp-match related-rx line))
     (list (string->symbol relation)
           (parse-position-text position)
           description))
   (for/list ([text (in-list (rest position-texts))])
     (match-define (list _ position label)
       (or (regexp-match labelled-rx text)
           (error 'terminal-parity "補足の位置行の形ではない: ~s" text)))
     (list (parse-position-text position) label))))

;; ---- LSP 側の取り出し --------------------------------------------------

;; renderer の表を借りず、逆向きの表を別に書く。
;; 借りると番号を取り違えた表がそのまま通る。
(define lsp-severity-symbols (hasheq 1 'error 2 'warning 3 'note))

;; percent-encoding を戻す。source-id->uri が復元できる形で encode している
;; ことも、この復号が通ることで確かめられる。
;; unreserved の側はすべて ASCII なので、1 文字が 1 byte である。
(define (uri->source-id-spelling uri)
  (unless (string-prefix? uri "topazolite:")
    (error 'uri->source-id-spelling "scheme が違う: ~s" uri))
  (define body (substring uri (string-length "topazolite:")))
  (let loop ([chars (string->list body)] [acc '()])
    (match chars
      ['() (bytes->string/utf-8 (list->bytes (reverse acc)))]
      [(list* #\% h l rest)
       (loop rest (cons (string->number (string h l) 16) acc))]
      [(cons c rest) (loop rest (cons (char->integer c) acc))])))

(define (jsexpr-value v) (if (eq? v (json-null)) #f v))

(define (range->ppos range spelling synthetic?)
  (define start (hash-ref range 'start))
  (ppos spelling synthetic?
        (hash-ref start 'line)
        (hash-ref start 'character)))

(define related-message-rx #px"^\\[([^]]+)\\] (.*)$")

(define (lsp-parity j)
  (define data (hash-ref j 'data))
  ;; message の第 1 行は title、以降は §8 の補足行である。
  ;; message が title と異なる fixture では本文行もここに並ぶが、terminal も
  ;; 同じ並びなので、接頭辞で拾う限り 2 形式の取り出しは同じ結果になる。
  (define message-lines (string-split (hash-ref j 'message) "\n" #:trim? #f))
  (define bodies (rest message-lines))
  (parity
   (hash-ref j 'code)
   (hash-ref lsp-severity-symbols (hash-ref j 'severity))
   (first message-lines)
   (range->ppos (hash-ref j 'range)
                (hash-ref data 'sourceId)
                (hash-ref data 'synthetic))
   (jsexpr-value (hash-ref data 'expected))
   (jsexpr-value (hash-ref data 'found))
   (lines-with-prefix bodies "note: ")
   (lines-with-prefix bodies "help: ")
   (for/list ([r (in-list (hash-ref j 'relatedInformation))])
     (match-define (list _ relation tail)
       (or (regexp-match related-message-rx (hash-ref r 'message))
           (error 'lsp-parity "relatedInformation の message の形ではない: ~s" r)))
     (define location (hash-ref r 'location))
     (define spelling (uri->source-id-spelling (hash-ref location 'uri)))
     (define synthetic? (string=? spelling "#:synthetic"))
     ;; marker は位置の情報であり description の一部ではない。
     ;; relation の角括弧とともに剥がす。
     (define description
       (if synthetic?
           (let ([m (regexp-match #px"^<synthetic> (.*)$" tail)])
             (unless m
               (error 'lsp-parity "synthetic の marker が無い: ~s" tail))
             (second m))
           tail))
     (list (string->symbol relation)
           (range->ppos (hash-ref location 'range) spelling synthetic?)
           description))
   (for/list ([lab (in-list (hash-ref data 'secondaryLabels))])
     (list (range->ppos (hash-ref lab 'range)
                        (hash-ref lab 'sourceId)
                        (hash-ref lab 'synthetic))
           (hash-ref lab 'message)))))

;; ---- JSON 側の取り出し -------------------------------------------------

;; JSON だけが byte offset を載せるため、span object から span を組み直して
;; span->location を通す。この変換の正しさは source-map-test.rkt が別に
;; 担保する。
(define (spelling->source-id spelling)
  (if (string=? spelling "#:synthetic") '#:synthetic (string->symbol spelling)))

(define (json-span->ppos span)
  (define spelling (hash-ref span 'sourceId))
  (define loc
    (span->location fixture-source-map
                    (list '#:span (spelling->source-id spelling)
                          (hash-ref span 'startByte)
                          (hash-ref span 'endByte))))
  (ppos spelling
        (location-synthetic? loc)
        (location-start-line loc)
        (location-start-character loc)))

(define (json-parity j)
  (parity
   (hash-ref j 'id)
   (string->symbol (hash-ref j 'severity))
   (hash-ref j 'title)
   (json-span->ppos (hash-ref j 'primarySpan))
   (jsexpr-value (hash-ref j 'expected))
   (jsexpr-value (hash-ref j 'found))
   (hash-ref j 'notes)
   (hash-ref j 'help)
   (for/list ([r (in-list (hash-ref j 'related))])
     (list (string->symbol (hash-ref r 'relation))
           (json-span->ppos (hash-ref r 'span))
           (hash-ref r 'description)))
   (for/list ([lab (in-list (hash-ref j 'secondaryLabels))])
     (list (json-span->ppos (hash-ref lab 'span))
           (hash-ref lab 'label)))))

;; ---- 比較 --------------------------------------------------------------

;; 観測量が 1 つも埋まらない fixture だけを並べると、parity は空同士の比較で
;; 通る。10 の観測量のうち、空になりうる 8 件について、値を持つ fixture が
;; 1 件以上あることを先に確かめる。code と severity と title は
;; diagnostic-schema-errors が空を弾くため、ここでは数えない。
(test-case
 "空になりうる 8 つの観測量は、いずれかの fixture で値を持つ"
 (define ps
   (for/list ([row (in-list fixture-table)])
     (json-parity (render-json (second row)))))
 (define (some pred) (for/or ([p (in-list ps)]) (and (pred p) #t)))
 (check-true (some parity-expected) "expected")
 (check-true (some parity-found) "found")
 (check-true (some (lambda (p) (pair? (parity-notes p)))) "notes")
 (check-true (some (lambda (p) (pair? (parity-help p)))) "help")
 (check-true (some (lambda (p) (= 2 (length (parity-related p))))) "related 2 件")
 (check-true (some (lambda (p) (= 2 (length (parity-secondary p)))))
             "secondary-labels 2 件")
 (check-true (some (lambda (p) (ppos-synthetic? (parity-position p))))
             "synthetic の primary")
 (check-true (some (lambda (p) (not (ppos-synthetic? (parity-position p)))))
             "実在の source の primary"))

(test-case
 "fixture 8 件で 3 形式の 10 観測量が一致する"
 (for ([row (in-list fixture-table)])
   (match-define (list name d) row)
   (define t (terminal-parity (render-terminal d fixture-source-map)))
   (define l (lsp-parity (render-lsp d fixture-source-map)))
   (define j (json-parity (render-json d)))
   (check-equal? t l (format "~a: terminal と LSP" name))
   (check-equal? l j (format "~a: LSP と JSON" name))))
