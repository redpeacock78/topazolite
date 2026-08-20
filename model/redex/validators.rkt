#lang racket

(require racket/match)

(provide validator-table
         validator-oid validator-name validator-proposition
         validator-payload-type validator-check
         validator-row-by-name validator-row-by-oid
         validator-row-by-proposition
         introduction-table projection-table
         introduction-row-by-name projection-row-by-name
         kernel-primitive-name?
         validator-error-message
         owned-free?
         copy-out-ok?
         literal-type)

;; validator 正典表。行は (oid nm φ τ check) の 5 つ組である。
;; R0 への発行者登録、primitive の型付けと δ 規則、ProofRep の発行者対応、
;; RVal の payload 束縛検査は、すべてこの表の行から生成する。表と検査規則の
;; 二重定義を作らないため、nm から oid への対応も表の外に置かない。
(define validator-table
  (list (list 'o-valid-port 'validPort '(Prop ValidPort) 'Int
              (lambda (payload)
                (and (exact-integer? payload)
                     (<= 1 payload 65535))))
        (list 'o-non-empty 'nonEmpty '(Prop NonEmpty) 'String
              (lambda (payload)
                (and (string? payload)
                     (positive? (string-length payload)))))))

(define (validator-oid row) (first row))
(define (validator-name row) (second row))
(define (validator-proposition row) (third row))
(define (validator-payload-type row) (fourth row))
(define (validator-check row) (fifth row))

(define (validator-row-by-name name)
  (findf (lambda (row) (eq? (validator-name row) name)) validator-table))

(define (validator-row-by-oid oid)
  (findf (lambda (row) (eq? (validator-oid row) oid)) validator-table))

(define (validator-row-by-proposition proposition)
  (findf (lambda (row) (equal? (validator-proposition row) proposition))
         validator-table))

;; 導入 primitive。型言語が型変数を持たないため、判定表に現れるペイロード型
;; ごとの単相 primitive として置く。行は (oid nm τ) である。
(define introduction-table
  (list (list 'o-untrusted-int 'untrustedInt 'Int)
        (list 'o-untrusted-string 'untrustedString 'String)))

;; 射影 primitive。判定表の行ごとに一つ置く。行は (oid nm φ τ) である。
(define projection-table
  (list (list 'o-unrefine-port 'unrefinePort '(Prop ValidPort) 'Int)
        (list 'o-unrefine-non-empty 'unrefineNonEmpty '(Prop NonEmpty)
              'String)))

(define (introduction-row-by-name name)
  (findf (lambda (row) (eq? (second row) name)) introduction-table))

(define (projection-row-by-name name)
  (findf (lambda (row) (eq? (second row) name)) projection-table))

;; 表の網羅性。判定表へ行を足したまま導入と射影を書き忘れると、primitive の
;; 無い命題や対応の無い oid が静かに残る。module 読み込み時に落とす。
(let ([payload-types
       (sort (map symbol->string
                  (remove-duplicates
                   (map validator-payload-type validator-table)))
             string<?)]
      [introduced
       (sort (map (lambda (row) (symbol->string (third row)))
                  introduction-table)
             string<?)])
  (unless (equal? payload-types introduced)
    (error 'validators
           "introduction-table does not cover the payload types: ~a vs ~a"
           payload-types introduced)))

(unless (equal?
         (map (lambda (row)
                (list (validator-proposition row)
                      (validator-payload-type row)))
              validator-table)
         (map (lambda (row) (list (third row) (fourth row)))
              projection-table))
  (error 'validators
         "projection-table does not cover the validator rows (proposition and type)"))

;; ペイロード型はリテラルで表せる型に限る。Owned-free でもリテラルを持たない
;; 型は payload 束縛検査が判定できないため、ここで落とす。
(for ([row (in-list validator-table)])
  (unless (memq (validator-payload-type row) '(Int String Unit))
    (error 'validators
           "validator payload type has no literal form: ~a"
           (validator-payload-type row))))

(define kernel-primitive-names
  (append (map validator-name validator-table)
          (map second introduction-table)
          (map second projection-table)))

(let ([oids (append (map validator-oid validator-table)
                    (map first introduction-table)
                    (map first projection-table))])
  (unless (= (length oids) (length (remove-duplicates oids)))
    (error 'validators "duplicate origin id in the tables: ~a" oids)))

(unless (= (length kernel-primitive-names)
           (length (remove-duplicates kernel-primitive-names)))
  (error 'validators "duplicate primitive name in the tables: ~a"
         kernel-primitive-names))

(define (kernel-primitive-name? name)
  (and (memq name kernel-primitive-names) #t))

;; δ の失敗側メッセージ。nm から決定的に構成し、環境や乱数を参照しない。
(define (validator-error-message name)
  (format "~a: rejected" name))

;; Untrusted と Refined のペイロード型は Owned を部分に含まない型に限る。
;; wrapper が affine 制約を隠すと、外層しか見ない既存の Owned 判定を素通りして
;; 資源を複製できてしまう。NFn の内部も含めて再帰する。
(define (effect-owned-free? effect)
  (match effect
    [`(Return ,_ ,type) (owned-free? type)]
    [`(Yield ,type) (owned-free? type)]
    [_ #t]))

(define (owned-free? type)
  (match type
    [`(Owned ,_) #f]
    [`(List ,element) (owned-free? element)]
    [`(Option ,element) (owned-free? element)]
    [`(Result ,ok-type ,error-type)
     (and (owned-free? ok-type) (owned-free? error-type))]
    [`(Untrusted ,payload) (owned-free? payload)]
    [`(Refined ,payload ,_) (owned-free? payload)]
    [`(Record ,row)
     (for/and ([field (in-list row)]) (owned-free? (second field)))]
    [`(Union ,left ,right) (and (owned-free? left) (owned-free? right))]
    [`(Intersection ,left ,right) (and (owned-free? left) (owned-free? right))]
    [`(NFn (,parameters ...) ,return-type (,effects ...) ,_)
     (and (for/and ([parameter (in-list parameters)]) (owned-free? parameter))
          (owned-free? return-type)
          (for/and ([effect (in-list effects)]) (effect-owned-free? effect)))]
    [_ #t]))

;; spec §6.2。Read の payload の条件。所有値も借用も含まない型である。
;; owned-free? と分ける理由は、owned-free? が Untrusted と Refined の
;; payload の検証にも使われており、そちらの意味を変えられないからである。
;; owned-free? は Borrowed と BorrowedMut の枝を持たず既定の #t へ落ちる。
;; 流用すると可変借用を含む値を複製でき、同じ place への可変借用が 2 つになる。
(define (effect-copy-out-ok? effect)
  (match effect
    [`(Return ,_ ,type) (copy-out-ok? type)]
    [`(Yield ,type) (copy-out-ok? type)]
    [_ #t]))

(define (copy-out-ok? type)
  (match type
    ['Int #t]
    ['Bool #t]
    ['Unit #t]
    ['String #t]
    ['Never #t]
    ['Res #t]
    [`(TypeInfo ,_) #t]
    [`(Proof ,_) #t]
    [`(Owned ,_) #f]
    [`(Borrowed ,_ ,_) #f]
    [`(BorrowedMut ,_ ,_) #f]
    [`(List ,element) (copy-out-ok? element)]
    [`(Option ,element) (copy-out-ok? element)]
    [`(Result ,ok-type ,error-type)
     (and (copy-out-ok? ok-type) (copy-out-ok? error-type))]
    [`(Untrusted ,payload) (copy-out-ok? payload)]
    [`(Refined ,payload ,_) (copy-out-ok? payload)]
    [`(Record ,row)
     (for/and ([field (in-list row)]) (copy-out-ok? (second field)))]
    [`(Union ,left ,right) (and (copy-out-ok? left) (copy-out-ok? right))]
    [`(Intersection ,left ,right)
     (and (copy-out-ok? left) (copy-out-ok? right))]
    [`(NFn (,parameters ...) ,return-type (,effects ...) ,_)
     (and (for/and ([parameter (in-list parameters)]) (copy-out-ok? parameter))
          (copy-out-ok? return-type)
          (for/and ([effect (in-list effects)]) (effect-copy-out-ok? effect)))]
    ;; 型構成子を追加するときは、複製の可否をここへ明示する。
    [_ #f]))

;; リテラルの型。判定表の τ に載りうる型だけを返し、それ以外は #f を返す。
(define (literal-type payload)
  (cond [(exact-integer? payload) 'Int]
        [(string? payload) 'String]
        [(eq? payload 'unit) 'Unit]
        [else #f]))
