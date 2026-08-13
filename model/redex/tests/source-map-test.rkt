#lang racket

(require rackunit
         "../source-map.rkt")

;; spec §18 第 1 群: ASCII のみ。
(test-case
 "ASCII のみの source は byte offset と列が一致する"
 (define sm (make-source-map (hasheq 'ascii "abc")))
 (define loc (span->location sm '(#:span ascii 0 3)))
 (check-equal? (location-source-id loc) 'ascii)
 (check-false (location-synthetic? loc))
 (check-equal? (location-start-line loc) 0)
 (check-equal? (location-start-character loc) 0)
 (check-equal? (location-end-line loc) 0)
 (check-equal? (location-end-character loc) 3))

;; spec §18 第 2 群: 多 byte 文字を含む行。
;; 「あいう」は 1 文字 3 byte なので、byte offset をそのまま列にした実装は
;; 3 と 6 を返す。
(test-case
 "多 byte 文字の行は byte offset と列が一致しない"
 (define sm (make-source-map (hasheq 'multi "あいう")))
 (define loc (span->location sm '(#:span multi 3 6)))
 (check-equal? (location-start-character loc) 1)
 (check-equal? (location-end-character loc) 2))

;; spec §18 第 3 群: 結合文字を含む行。
;; e と U+0301 は 1 つの書記素だが 2 つの scalar である。
;; 書記素で数える実装は end の列に 1 を返す。
(test-case
 "結合文字は 2 つの code unit として数える"
 (define source (string #\e #\u0301 #\f))
 (define sm (make-source-map (hasheq 'comb source)))
 (check-equal? (bytes-length (string->bytes/utf-8 source)) 4)
 (define loc (span->location sm '(#:span comb 0 3)))
 (check-equal? (location-start-character loc) 0)
 (check-equal? (location-end-character loc) 2))

;; spec §18 第 4 群: 基本多言語面の外にある絵文字。
;; byte 数と scalar 数と UTF-16 code unit 数の 3 つがすべて異なる行である。
;; 3 つの単位を取り違える実装は、この 1 行で落ちる。
(test-case
 "絵文字の行は byte と scalar と code unit の 3 つが異なる"
 (define source "a😀b")
 (check-equal? (bytes-length (string->bytes/utf-8 source)) 6)
 (check-equal? (string-length source) 3)
 (check-equal? (utf-16-length source) 4)
 (define sm (make-source-map (hasheq 'emoji source)))
 (define loc (span->location sm '(#:span emoji 1 5)))
 (check-equal? (location-start-character loc) 1)
 ;; 絵文字は 2 code unit なので end は 3 である。
 ;; scalar で数える実装は 2、byte で数える実装は 5 を返す。
 (check-equal? (location-end-character loc) 3)
 (define whole (span->location sm '(#:span emoji 0 6)))
 (check-equal? (location-end-character whole) 4))

;; spec §18 第 5 群: 複数行の source。
(test-case
 "改行をまたぐ span は行と列の双方が動く"
 (define sm (make-source-map (hasheq 'lines "ab\ncd\nef")))
 (define loc (span->location sm '(#:span lines 3 7)))
 (check-equal? (location-start-line loc) 1)
 (check-equal? (location-start-character loc) 0)
 (check-equal? (location-end-line loc) 2)
 (check-equal? (location-end-character loc) 1)
 ;; 最後の改行より後ろだけを数えない実装は、start の列に 3 を返す。
 (define head (span->location sm '(#:span lines 0 2)))
 (check-equal? (location-start-line head) 0)
 (check-equal? (location-end-character head) 2))

;; spec §18 第 6 群: 境界の規則。
;; span の 11 行と make-source-map の 6 行で合わせて 17 行である。
;; 境界外と文字途中は startByte の側と endByte の側を別の行に置く。
;; 片側だけを検査した実装が通る余地を残さないためである。
(define boundary-source-map (make-source-map (hasheq 'multi "あい")))

(define boundary-span-table
  (list
   (list "endByte が byte 長と等しい" '(#:span multi 0 6) 'pass)
   (list "startByte と endByte がともに byte 長と等しい" '(#:span multi 6 6) 'pass)
   (list "startByte が byte 長を超える" '(#:span multi 7 7) 'error)
   (list "endByte だけが byte 長を超える" '(#:span multi 0 7) 'error)
   (list "startByte が多 byte 文字の途中を指す" '(#:span multi 1 6) 'error)
   (list "endByte だけが多 byte 文字の途中を指す" '(#:span multi 0 4) 'error)
   (list "startByte が endByte より大きい" '(#:span multi 4 2) 'error)
   (list "source-map に無い sourceId" '(#:span absent 0 0) 'error)
   (list "synthetic の startByte が endByte より大きい"
         '(#:span #:synthetic 5 2) 'error)
   (list "synthetic の要素が自然数でない" '(#:span #:synthetic -1 0) 'error)
   (list "synthetic の空 span" '(#:span #:synthetic 0 0) 'synthetic)))

(test-case
 "span->location の境界の 11 行"
 (for ([row (in-list boundary-span-table)])
   (match-define (list name span expectation) row)
   (case expectation
     [(pass)
      (check-pred location? (span->location boundary-source-map span) name)]
     [(error)
      (check-exn exn:fail?
                 (lambda () (span->location boundary-source-map span))
                 name)]
     [(synthetic)
      (define loc (span->location boundary-source-map span))
      (check-true (location-synthetic? loc) name)
      (check-equal? (list (location-start-line loc)
                          (location-start-character loc)
                          (location-end-line loc)
                          (location-end-character loc))
                    '(0 0 0 0)
                    name)])))

(define source-map-input-table
  (list
   (list "key に keyword を含む" (hasheq '#:synthetic "a") 'error)
   (list "key に整数を含む" (hash 1 "a") 'error)
   (list "value に文字列でない値を含む" (hasheq 'a 1) 'error)
   (list "key の記号名に改行を含む" (hasheq (string->symbol "a\nb") "a") 'error)
   (list "value に CR を含む" (hasheq 'a "a\rb") 'error)
   (list "空の hash" (hasheq) 'pass)))

(test-case
 "make-source-map の入力の 6 行"
 (for ([row (in-list source-map-input-table)])
   (match-define (list name table expectation) row)
   (case expectation
     [(pass) (check-pred source-map? (make-source-map table) name)]
     [(error) (check-exn exn:fail? (lambda () (make-source-map table)) name)])))

;; 検査を構築の時点へ置いたことを、error の who で言明する。
;; span->location まで遅らせた実装は、表の作り手の誤りを表を引く側の error として
;; 報告するため、この 2 行で落ちる。
(test-case
 "表の誤りは make-source-map の error として現れる"
 (check-exn #rx"make-source-map"
            (lambda () (make-source-map (hasheq 'a 1))))
 (check-exn #rx"source-map に無い sourceId"
            (lambda () (span->location boundary-source-map '(#:span absent 0 0)))))
