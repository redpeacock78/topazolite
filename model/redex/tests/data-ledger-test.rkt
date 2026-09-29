#lang racket

(require rackunit
         redex/reduction-semantics
         "../data-env.rkt"
         "../origins.rkt"
         "../traits.rkt")

(define (no-fail reason kind key)
  (error 'test "~s ~s ~s" reason kind key))

(define (first-failure decls)
  (let/ec k
    (make-trait-ledger canonical-trait-env
                       #:data decls
                       #:fail (lambda (reason kind key) (k (list reason key))))
    'ok))

(define (decl name parameters . constructors)
  (list name parameters constructors))
(define (ctor name . fields)
  (list name fields))

(define pair-decl
  (decl 'Pair '(A B) (ctor 'mkpair '(Param A) '(Param B))))
(define nat-decl
  (decl 'Nat '() (ctor 'zero) (ctor 'succ '(Data Nat ()))))
(define even-decl
  (decl 'Even '(A) (ctor 'enil)
        (ctor 'econs '(Param A) '(Data Odd ((Param A))))))
(define odd-decl
  (decl 'Odd '(B) (ctor 'ocons '(Param B) '(Data Even ((Param B))))))

(test-case "正しい宣言は台帳に載り、schema を置換して返す"
  (define ledger
    (make-trait-ledger canonical-trait-env
                       #:data (list pair-decl nat-decl even-decl odd-decl)
                       #:fail no-fail))
  (call-with-trait-ledger
   ledger
   (lambda ()
     (check-equal? (data-schema 'Pair '(Int Bool)) '((mkpair (Int Bool))))
     (check-equal? (data-constructor 'succ) '(Nat 1))
     (check-equal? (data-schema 'Even '(Int))
                   '((enil ()) (econs (Int (Data Odd (Int))))))
     (check-equal? (data-field-types 'Even '(Int))
                   '(Int (Data Odd (Int))))
     (check-false (data-schema 'Pair '(Int)))
     (check-false (data-schema 'Missing '())))))

(test-case "既定の台帳では data 型が空である"
  (check-false (data-decl 'Pair))
  (check-false (data-constructor 'mkpair)))

(test-case "custom の索引をキャッシュ有効のまま読むと error"
  (define ledger
    (make-trait-ledger canonical-trait-env #:data (list nat-decl) #:fail no-fail))
  (call-with-trait-ledger ledger
    (lambda ()
      (parameterize ([caching-enabled? #t])
        (check-exn exn:fail? (lambda () (current-data-index)))))))

(test-case "§11 の reason を最小の宣言で報告する"
  (define cases
    (list
     (list 'duplicate-data-type (list nat-decl nat-decl))
     (list 'reserved-data-type (list (decl 'List '() (ctor 'mk))))
     (list 'duplicate-constructor
           (list (decl 'A '() (ctor 'k)) (decl 'B '() (ctor 'k))))
     (list 'duplicate-constructor (list (decl 'C '() (ctor 'some))))
     (list 'duplicate-type-parameter (list (decl 'P '(X X) (ctor 'mk))))
     (list 'unknown-type-parameter
           (list (decl 'P '(X) (ctor 'mk '(Param Y)))))
     (list 'empty-data-type (list (decl 'E '())))
     (list 'data-arity-mismatch
           (list (decl 'P '(X) (ctor 'mk '(Data P ())))))
     (list 'unknown-data-type
           (list (decl 'P '() (ctor 'mk '(Data Q ())))))
     (list 'irregular-recursion
           (list (decl 'N '(A) (ctor 'mk '(Data N ((List (Param A))))))))
     (list 'irregular-recursion
           (list (decl 'E1 '(A) (ctor 'a '(Data O1 ())))
                 (decl 'O1 '() (ctor 'b '(Data E1 (Int))))))
     (list 'non-positive-recursion
           (list (decl 'Bad '()
                       (ctor 'mk '(NFn ((Data Bad ())) Int () () () User)))))
     (list 'non-positive-recursion
           (list (decl 'Bad '()
                       (ctor 'mk '(Record ((x (Data Bad ()) mut)))))))
     (list 'non-positive-recursion
           (list (decl 'Bad '()
                       (ctor 'mk '(RawPtr (Data Bad ()) Const NonNull
                                           (Align 1) (AddrSpace native) (Prov p))))))
     ;; 強連結成分外の S の仮引数が S の中で負の位置にあれば、S の型引数は負の位置である。
     (list 'non-positive-recursion
           (list (decl 'Neg '(A)
                       (ctor 'mk '(NFn ((Param A)) Int () () () User)))
                 (decl 'T '() (ctor 'leaf)
                       (ctor 'node '(Data Neg ((Data T ())))))))
     (list 'unbound-region-in-field
           (list (decl 'F '() (ctor 'mk '(Borrowed Int (RParam r))))))
     (list 'ill-formed-field-type
           (list (decl 'F '() (ctor 'mk '(Untrusted (Owned Int))))))))
  (for ([entry (in-list cases)])
    (check-equal? (first (first-failure (second entry)))
                  (first entry)
                  (format "~s" (second entry)))))

(test-case "失敗の key は T K 欄番号 型仮引数の 4 つ組"
  (define cases
    (list
     (list (list nat-decl nat-decl) '(duplicate-data-type (Nat #f #f #f)))
     (list (list (decl 'List '() (ctor 'mk)))
           '(reserved-data-type (List #f #f #f)))
     (list (list (decl 'A '() (ctor 'k)) (decl 'B '() (ctor 'j) (ctor 'k)))
           '(duplicate-constructor (B k #f #f)))
     (list (list (decl 'C '() (ctor 'some)))
           '(duplicate-constructor (C some #f #f)))
     (list (list (decl 'P '(X Y X) (ctor 'mk)))
           '(duplicate-type-parameter (P #f #f X)))
     (list (list (decl 'P '(X) (ctor 'mk 'Int '(Data P ()))))
           '(data-arity-mismatch (P mk 1 #f)))
     (list (list (decl 'P '() (ctor 'a) (ctor 'b 'Int '(Data Q ()))))
           '(unknown-data-type (P b 1 #f)))
     (list (list (decl 'N '(A) (ctor 'z) (ctor 'mk 'Int
                                       '(Data N ((List (Param A)))))))
           '(irregular-recursion (N mk 1 #f)))
     (list (list (decl 'Bad '() (ctor 'z) (ctor 'mk 'Int
                                         '(NFn ((Data Bad ())) Int () () () User))))
           '(non-positive-recursion (Bad mk 1 #f)))
     (list (list (decl 'F '() (ctor 'a) (ctor 'mk 'Int '(Borrowed Int (RParam r)))))
           '(unbound-region-in-field (F mk 1 #f)))
     (list (list (decl 'F '() (ctor 'a)
                       (ctor 'mk 'Int '(Untrusted (Owned Int)))))
           '(ill-formed-field-type (F mk 1 #f)))))
  (check-equal? (first-failure (list (decl 'P '(X) (ctor 'mk '(Param Y)))))
                '(unknown-type-parameter (P mk 0 Y)))
  (check-equal? (first-failure (list (decl 'E '())))
                '(empty-data-type (E #f #f #f)))
  (for ([entry (in-list cases)])
    (check-equal? (first-failure (first entry))
                  (second entry)
                  (format "~s" (first entry)))))

(test-case "正の位置の再帰は受理する"
  (define cases
    (list
     (list even-decl odd-decl)
     (list (decl 'T '() (ctor 'leaf) (ctor 'node '(Owned (Data T ())) 'Int)))
     (list (decl 'T '() (ctor 'leaf) (ctor 'node '(List (Data T ())))))
     (list (decl 'T '() (ctor 'leaf)
                 (ctor 'node '(Record ((l (Data T ()) imm))))))
     (list (decl 'T '() (ctor 'leaf)
                 (ctor 'next '(NFn (Unit) (Data T ()) () () () User))))
     (list (decl 'F '()
                 (ctor 'mk '(ForallRegion (r)
                                           (NFn ((Borrowed Int (RParam r)))
                                                Int () () () User)))))
     (list (decl 'W '(A) (ctor 'w '(Untrusted (Param A)))))
     ;; 強連結成分外の S の仮引数が S の中で正の位置にだけあれば、S の型引数は正の位置である。
     (list (decl 'Box '(A) (ctor 'mk '(Param A)))
           (decl 'T '() (ctor 'leaf)
                 (ctor 'node '(Data Box ((Data T ()))))))))
  (for ([decls (in-list cases)])
    (check-equal? (first-failure decls) 'ok (format "~s" decls))))
