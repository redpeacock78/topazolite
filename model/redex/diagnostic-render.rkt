#lang racket

(provide format-unfixed
         unfixed->jsexpr
         source-id->uri
         span->jsexpr
         render-terminal
         render-lsp
         render-json)

(require json
         racket/match
         racket/string
         "diagnostic.rkt"
         "source-map.rkt")

;; spec §11: 形を固定しない 4 欄（expected、found、effect-context、
;; proof-context）の整形。3 つの renderer がこの 1 つの関数を共有する。
;; ~a ではなく ~s を使うのは、文字列と記号を見分けられるようにするためである。
;; capability-diagnostic の reason は文字列で found へ入るため、~a にすると
;; 型項の記号と区別が付かない。
(define (format-unfixed v)
  (format "~s" v))

;; #f は「値が無い」を表す。#f そのものを表示すると、found が偽値であった診断と
;; 区別が付かない。
(define (unfixed->jsexpr v)
  (if v (format-unfixed v) (json-null)))

(define (synthetic-sid? sid)
  (eq? sid '#:synthetic))

;; #:synthetic は keyword なので symbol->string を使えない。
;; 綴りは JSON の span object と LSP の data で同じにする。
(define (sid-spelling sid)
  (if (synthetic-sid? sid) "#:synthetic" (symbol->string sid)))

;; spec §10 の span object。JSON と LSP の data が同じ形を使う。
(define (span->jsexpr span)
  (match-define (list '#:span sid start end) span)
  (hasheq 'sourceId (sid-spelling sid)
          'startByte start
          'endByte end
          'synthetic (synthetic-sid? sid)))

;; spec §9: sourceId から URI への変換。
;; (format "topazolite:~a" sid) の形は採らない。#:synthetic の # が fragment の
;; 区切りになり、URI から sourceId を復元できない。
;; RFC 3986 の unreserved 以外の byte をすべて %XX の 2 桁大文字 16 進へ写す。
(define unreserved-bytes
  (list->seteqv
   (bytes->list
    #"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-._~")))

(define (percent-encode-byte b)
  (string-upcase
   (if (< b 16)
       (format "%0~a" (number->string b 16))
       (format "%~a" (number->string b 16)))))

;; 変換を 1 つの関数へ閉じる。LSP renderer の 2 箇所で組むと、片方だけが
;; encoding を欠いた形になる。
(define (source-id->uri sid)
  (string-append
   "topazolite:"
   (apply string-append
          (for/list ([b (in-bytes (string->bytes/utf-8 (sid-spelling sid)))])
            (if (set-member? unreserved-bytes b)
                (string (integer->char b))
                (percent-encode-byte b))))))

;; spec §8 の補足行の第 1 行から第 7 行。位置を持たない欄だけを、表の順に並べる。
;; terminal は各行へ "  = " を付け、LSP の message は接頭辞なしで同じ list を
;; 並べる。2 箇所で組むと、片方だけが欄を落とした形になる。
(define (supplement-bodies d)
  (append
   ;; 第 1 行。message が title と同じときは 2 度出さない。
   (if (equal? (diagnostic-message d) (diagnostic-title d))
       '()
       (string-split (diagnostic-message d) "\n" #:trim? #f))
   (if (diagnostic-expected d)
       (list (format "expected: ~a" (format-unfixed (diagnostic-expected d))))
       '())
   (if (diagnostic-found d)
       (list (format "found: ~a" (format-unfixed (diagnostic-found d))))
       '())
   (if (diagnostic-effect-context d)
       (list (format "effect: ~a"
                     (format-unfixed (diagnostic-effect-context d))))
       '())
   (if (diagnostic-proof-context d)
       (list (format "proof: ~a"
                     (format-unfixed (diagnostic-proof-context d))))
       '())
   (for/list ([note (in-list (diagnostic-notes d))])
     (format "note: ~a" note))
   (for/list ([h (in-list (diagnostic-help d))])
     (format "help: ~a" h))))

;; spec §8 の位置欄。1 起点へ直すのは terminal だけである。
;; synthetic へ 1:1 を書くと source の先頭を指す実在の位置と区別できない。
(define (position-text loc)
  (if (location-synthetic? loc)
      "<synthetic>"
      (format "~a:~a:~a"
              (sid-spelling (location-source-id loc))
              (add1 (location-start-line loc))
              (add1 (location-start-character loc)))))

;; 抜粋は primary span の開始行 1 行だけである。
;; 末尾の改行の後ろの空行も 1 行として数える。span の末尾 offset はその位置を
;; 指しうるため、行が無いものとして扱うと抜粋が欠ける。
(define (source-line src line-index)
  (define lines (string-split src "\n" #:trim? #f))
  (if (< line-index (length lines))
      (list-ref lines line-index)
      ""))

;; caret の桁合わせは UTF-16 code unit で行う。表示幅で揃えるのは Phase 2 以降の
;; Ariadne の仕事であり、位置行の列と同じ単位にしておけば両者が食い違わない。
(define (caret-line loc line-text)
  (define start (location-start-character loc))
  (define width
    (cond
      ;; 複数行 span は開始列から行末までとする。開始列が行末に等しいときも
      ;; caret を 1 本は出す。0 本にすると caret 行が空行と区別できなくなる。
      [(not (= (location-start-line loc) (location-end-line loc)))
       (max 1 (- (utf-16-length line-text) start))]
      ;; 空 span は 1 文字分とする。
      [(= start (location-end-character loc)) 1]
      [else (- (location-end-character loc) start)]))
  (string-append (make-string start #\space) (make-string width #\^)))

;; spec §8: ANSI escape を含まない plain text を返す。末尾に改行を置かない。
(define (render-terminal d sm)
  (define loc (span->location sm (diagnostic-primary-span d)))
  (define header
    (format "~a[~a]: ~a"
            (diagnostic-severity d) (diagnostic-id d) (diagnostic-title d)))
  (define position (format "  --> ~a" (position-text loc)))
  (define excerpt
    (if (location-synthetic? loc)
        '()
        (let ([line-text
               (source-line (source-map-source sm (location-source-id loc))
                            (location-start-line loc))])
          (list line-text (caret-line loc line-text)))))
  (define label-lines
    (for/list ([lab (in-list (diagnostic-secondary-labels d))])
      (match-define (list span label) lab)
      (format "  --> ~a: ~a" (position-text (span->location sm span)) label)))
  (define related-lines
    (for/list ([r (in-list (diagnostic-related d))])
      (match-define (list relation span description) r)
      (format "  = related[~a] ~a: ~a"
              relation (position-text (span->location sm span)) description)))
  (define backend-lines
    (if (diagnostic-backend d)
        (list (format "  = backend: ~a" (diagnostic-backend d)))
        '()))
  (string-join
   (append (list header position)
           excerpt
           label-lines
           (for/list ([body (in-list (supplement-bodies d))])
             (string-append "  = " body))
           related-lines
           backend-lines)
   "\n"))

;; spec §9: severity の 3 語を LSP の番号へ写す。
(define lsp-severity-numbers (hasheq 'error 1 'warning 2 'note 3))

;; location から LSP の range を作る。synthetic を特別扱いしない。
;; span->location が synthetic へ 4 つの 0 を返すため、同じ経路で
;; (0,0)-(0,0) になる。ここで分岐を置くと location の規則と二重管理になる。
(define (location->range loc)
  (hasheq 'start (hasheq 'line (location-start-line loc)
                         'character (location-start-character loc))
          'end (hasheq 'line (location-end-line loc)
                       'character (location-end-character loc))))

;; source-chain の frame を object へ写す。LSP の data と JSON の sourceChain が
;; 同じ関数を読む。
(define (frame->jsexpr frame)
  (match-define (list phase kind span) frame)
  (hasheq 'phase (symbol->string phase)
          'kind (symbol->string kind)
          'span (span->jsexpr span)))

(define (symbol-or-null v)
  (if v (symbol->string v) (json-null)))

;; spec §9: LSP の Diagnostic に対応する hasheq を返す。
;; top level の uri は置かない。uri は publishDiagnostics の params が持つ。
(define (render-lsp d sm)
  (define primary (diagnostic-primary-span d))
  (define loc (span->location sm primary))
  (match-define (list '#:span sid start-byte end-byte) primary)
  (hasheq
   'range (location->range loc)
   'severity (hash-ref lsp-severity-numbers (diagnostic-severity d))
   'code (diagnostic-id d)
   'source "topazolite"
   ;; 位置は range と relatedInformation が持つので message へは入れない。
   'message (string-join (cons (diagnostic-title d) (supplement-bodies d)) "\n")
   'relatedInformation
   (for/list ([r (in-list (diagnostic-related d))])
     (match-define (list relation span description) r)
     (define r-loc (span->location sm span))
     (hasheq 'location
             (hasheq 'uri (source-id->uri (location-source-id r-loc))
                     'range (location->range r-loc))
             ;; DiagnosticRelatedInformation は location と message の 2 欄しか
             ;; 持たない。relation を data へ隠すと client 上で消えるため、
             ;; message の接頭辞として載せる。
             'message (if (location-synthetic? r-loc)
                          (format "[~a] <synthetic> ~a" relation description)
                          (format "[~a] ~a" relation description))))
   'data
   (hasheq
    'synthetic (location-synthetic? loc)
    'sourceId (sid-spelling sid)
    'startByte start-byte
    'endByte end-byte
    'category (symbol->string (diagnostic-category d))
    'schemaVersion diagnostic-schema-version
    'backend (symbol-or-null (diagnostic-backend d))
    'expected (unfixed->jsexpr (diagnostic-expected d))
    'found (unfixed->jsexpr (diagnostic-found d))
    'secondaryLabels
    (for/list ([lab (in-list (diagnostic-secondary-labels d))])
      (match-define (list span label) lab)
      (define l-loc (span->location sm span))
      ;; span を raw のまま置かない。LSP の出力の中で位置の単位が 2 種類になる。
      ;; sourceId を載せるのは、range だけでは参照先の source を特定できない
      ;; ためである。top level の range は data の sourceId と対で読むのに、
      ;; ここだけ対の片方を欠くと、別 source の label を同じ位置として扱う
      ;; 受け手を許してしまう。
      (hasheq 'range (location->range l-loc)
              'message label
              'sourceId (sid-spelling (location-source-id l-loc))
              'synthetic (location-synthetic? l-loc)))
    'sourceChain (map frame->jsexpr (diagnostic-source-chain d))
    'effectContext (unfixed->jsexpr (diagnostic-effect-context d))
    'proofContext (unfixed->jsexpr (diagnostic-proof-context d)))))

;; spec §10: Diagnostic の 18 欄をすべて写し、schemaVersion と registryVersion を
;; 最上位へ置く。受け手が、どの版の形で書かれた object かを入力自身から判定できる
;; ようにするためである。
;; source-map を取らないのは、span object が byte offset をそのまま載せる形だから
;; である。
(define (render-json d)
  (hasheq
   ;; 第 1 群。素の値の 6 欄（id、severity、category、title、message、backend）。
   'id (diagnostic-id d)
   'severity (symbol->string (diagnostic-severity d))
   'category (symbol->string (diagnostic-category d))
   'title (diagnostic-title d)
   'message (diagnostic-message d)
   'backend (symbol-or-null (diagnostic-backend d))
   ;; 第 2 群。構造化された 4 欄、文字列の list の 2 欄、空の list の 2 欄。
   'primarySpan (span->jsexpr (diagnostic-primary-span d))
   'secondaryLabels
   (for/list ([lab (in-list (diagnostic-secondary-labels d))])
     (match-define (list span label) lab)
     (hasheq 'span (span->jsexpr span) 'label label))
   'sourceChain (map frame->jsexpr (diagnostic-source-chain d))
   'related
   (for/list ([r (in-list (diagnostic-related d))])
     (match-define (list relation span description) r)
     (hasheq 'relation (symbol->string relation)
             'span (span->jsexpr span)
             'description description))
   'notes (diagnostic-notes d)
   'help (diagnostic-help d)
   ;; schema version 3 は空を要求する。要素形が定まる時点でここを写し方へ変え、
   ;; schema version を上げる。
   'expansionTrace '()
   'fixes '()
   ;; 第 3 群。形を固定しない 4 欄。
   'expected (unfixed->jsexpr (diagnostic-expected d))
   'found (unfixed->jsexpr (diagnostic-found d))
   'effectContext (unfixed->jsexpr (diagnostic-effect-context d))
   'proofContext (unfixed->jsexpr (diagnostic-proof-context d))
   'schemaVersion diagnostic-schema-version
   'registryVersion diagnostic-registry-version))
