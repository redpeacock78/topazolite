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
 "lex は bytes を受け、lex/string は同じ結果を返す"
 (check-equal? (lex 'src #"a b") (lex/string 'src "a b")))
