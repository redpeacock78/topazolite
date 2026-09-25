#lang racket

(require rackunit
         "../lexer.rkt"
         "../diagnostic.rkt")

(define (kinds str)
  (map stok-kind (lex/string 'src str)))

(define (spans str)
  (map stok-span (lex/string 'src str)))

(test-case
 "空入力は eof だけを返す"
 (check-equal? (kinds "") '(eof))
 (check-equal? (spans "") '((#:span src 0 0))))

(test-case
 "識別子と予約語と記号と整数と文字列を字句化する"
 (check-equal? (kinds "let x = 1") '(kw ident punct int eof))
 (check-equal? (kinds "\"ab\"") '(str eof))
 (check-equal? (map stok-value (lex/string 'src "let x = 1"))
               '(let x = 1 eof)))

(test-case
 "文字列の値はエスケープを展開し、span は quote を含む"
 (define toks (lex/string 'src "\"a\\nb\""))
 (check-equal? (stok-value (first toks)) "a\nb")
 ;; 文字列の入力は 6 byte（開き quote、a、\\、n、b、閉じ quote）である。
 (check-equal? (stok-span (first toks)) '(#:span src 0 6)))

(test-case
 "整数の値は正確な非負整数である"
 (check-equal? (stok-value (first (lex/string 'src "007"))) 7))

(test-case
 "連続する改行は 1 つの nl へ畳み、span は run 全体を覆う"
 (check-equal? (kinds "a\n\n\nb") '(ident nl ident eof))
 (check-equal? (second (spans "a\n\n\nb")) '(#:span src 1 4)))

(test-case
 "行コメントは token を作らず、改行は残り nl の span が run を覆う"
 (check-equal? (kinds "a\n// c\nb") '(ident nl ident eof))
 (check-equal? (second (spans "a\n// c\nb")) '(#:span src 1 7)))

(test-case
 "空白とタブは token を作らない"
 (check-equal? (kinds "a \t b") '(ident ident eof)))

(test-case
 "let と mut は別の kw token であり畳まない"
 (check-equal? (map stok-value (lex/string 'src "let mut"))
               '(let mut eof)))

(test-case
 "trait と impl と for と derive は kw である"
 (check-equal? (kinds "trait impl for derive") '(kw kw kw kw eof))
 (check-equal? (map stok-value (lex/string 'src "trait impl for derive"))
               '(trait impl for derive eof)))

(test-case
 "SUR-011: -> は 2 byte の記号であり、不完全な形は字句エラーになる"
 (check-equal? (kinds "fn() -> Int") '(kw punct punct punct ident eof))
 ;; a は 0-1、-> は 1-3、b は 3-4。
 (check-equal? (take (spans "a->b") 3)
               '((#:span src 0 1) (#:span src 1 3) (#:span src 3 4)))
 (for ([src (in-list '("- >" "-" ">" "=>"))]
       [at  (in-list '(0 0 0 1))])
   (define d (lex/string 'src src))
   (check-equal? (diagnostic-id d) "E-SUR-002")
   (check-equal? (diagnostic-primary-span d)
                 `(#:span src ,at ,(add1 at)))))

(test-case
 "lex は bytes を受け、lex/string は同じ結果を返す"
 (check-equal? (lex 'src #"a b") (lex/string 'src "a b")))

(define (lex-code id bs)
  (define r (lex id bs))
  (and (diagnostic? r) (diagnostic-id r)))

(define (lex-primary id bs)
  (diagnostic-primary-span (lex id bs)))

(define (lex/string-code id str)
  (define r (lex/string id str))
  (and (diagnostic? r) (diagnostic-id r)))

(test-case
 "不正な byte は E-SUR-001 であり、primary span は byte 1 個を指す"
 (check-equal? (lex-code 'src (bytes 97 255 98)) "E-SUR-001")
 (check-equal? (lex-primary 'src (bytes 97 255 98)) '(#:span src 1 2)))

(test-case
 "不正な byte は位置によらず他の字句の誤りより先に返る"
 ;; @ は位置 0 の E-SUR-002 だが、後方の不正 byte が優先する。
 (check-equal? (lex-code 'src (bytes 64 255)) "E-SUR-001")
 (check-equal? (lex-primary 'src (bytes 64 255)) '(#:span src 1 2)))

(test-case
 "字句にならない文字は E-SUR-002 であり、span は code point の byte 列を覆う"
 (check-equal? (lex-code 'src #"a + b") "E-SUR-002")
 (check-equal? (lex-primary 'src #"a + b") '(#:span src 2 3))
 ;; U+FFFD は正しい UTF-8 なので E-SUR-001 ではない。3 byte を覆う。
 (check-equal? (lex-code 'src (string->bytes/utf-8 "�")) "E-SUR-002")
 (check-equal? (lex-primary 'src (string->bytes/utf-8 "�"))
               '(#:span src 0 3)))

(test-case
 "復帰文字は字句にならない"
 (check-equal? (lex-code 'src #"a\r\nb") "E-SUR-002"))

(test-case
 "単独の斜線は E-SUR-002 であり、二重の斜線はコメントである"
 (check-equal? (lex-code 'src #"a / b") "E-SUR-002")
 (check-equal? (map stok-kind (lex 'src #"a // b")) '(ident eof)))

(test-case
 "閉じない文字列は E-SUR-003 であり、span は開き quote から停止位置までである"
 (check-equal? (lex-code 'src #"\"ab") "E-SUR-003")
 (check-equal? (lex-primary 'src #"\"ab") '(#:span src 0 3))
 ;; 改行で止まる場合、改行の byte 位置は含めない。
 (check-equal? (lex-primary 'src #"\"ab\nc\"") '(#:span src 0 3)))

(test-case
 "許さないエスケープは E-SUR-004 であり、span は次の code point の末尾までである"
 (check-equal? (lex-code 'src #"\"a\\q\"") "E-SUR-004")
 (check-equal? (lex-primary 'src #"\"a\\q\"") '(#:span src 2 4))
 (check-equal? (lex-primary 'src (string->bytes/utf-8 "\"a\\�\""))
               '(#:span src 2 6)))

(test-case
 "許さないエスケープは閉じない文字列より先に返る"
 (check-equal? (lex-code 'src #"\"a\\q") "E-SUR-004"))

(test-case
 "逆斜線が入力の末尾や改行の手前にある場合は E-SUR-003 である"
 (check-equal? (lex-code 'src #"\"a\\") "E-SUR-003")
 (check-equal? (lex-code 'src #"\"a\\\n\"") "E-SUR-003"))

(test-case
 "lex/string の経路では E-SUR-001 へ到達しない"
 ;; lex/string は string->bytes/utf-8 を通すので、入力は常に正しい UTF-8 に
 ;; なる。置換文字を含む文字列でも不正 byte にはならず、字句にならない文字
 ;; として E-SUR-002 で止まる。
 (check-equal? (lex/string-code 'src "a") #f)
 (check-equal? (lex/string-code 'src "�") "E-SUR-002"))

(test-case
 "source map へ登録する文字列は byte 長と後続の byte 位置を保つ"
 ;; spec §4.4。診断は生の byte 列から作り、描画は source map の文字列から
 ;; 行う。#\? は UTF-8 1 byte なので、置き換えても byte 長と、置換位置より
 ;; 後ろのすべての byte 位置が変わらない。
 (define bs (bytes 97 255 98))
 (define str (bytes->string/utf-8 bs #\?))
 (check-equal? str "a?b")
 (check-equal? (bytes-length (string->bytes/utf-8 str)) (bytes-length bs))
 ;; E-SUR-001 の primary span [1, 2) が、置換後の文字列でも同じ byte を指す。
 (check-equal? (lex-primary 'src bs) '(#:span src 1 2))
 (check-equal? (subbytes (string->bytes/utf-8 str) 1 2) #"?")
 ;; 非 ASCII が前にあっても同じである。
 (define bs2 (bytes-append (string->bytes/utf-8 "é") (bytes 255 98)))
 (check-equal? (bytes-length (string->bytes/utf-8 (bytes->string/utf-8 bs2 #\?)))
               (bytes-length bs2)))
