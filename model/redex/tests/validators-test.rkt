#lang racket
(require rackunit "../validators.rkt")

;; RFN-001: 名前・oid・命題のどれから引いても同じ行に着く。
(let ([row (validator-row-by-name 'validPort)])
  (check-equal? (validator-oid row) 'o-valid-port)
  (check-equal? (validator-proposition row) '(Prop ValidPort))
  (check-equal? (validator-payload-type row) 'Int)
  (check-eq? row (validator-row-by-oid 'o-valid-port))
  (check-eq? row (validator-row-by-proposition '(Prop ValidPort))))

(let ([row (validator-row-by-name 'nonEmpty)])
  (check-equal? (validator-oid row) 'o-non-empty)
  (check-equal? (validator-proposition row) '(Prop NonEmpty))
  (check-equal? (validator-payload-type row) 'String)
  (check-eq? row (validator-row-by-oid 'o-non-empty))
  (check-eq? row (validator-row-by-proposition '(Prop NonEmpty))))

;; RFN-001: check は境界値を含めて決定的である。
(let ([check-port (validator-check (validator-row-by-name 'validPort))])
  (check-true (check-port 1))
  (check-true (check-port 65535))
  (check-false (check-port 0))
  (check-false (check-port 65536))
  (check-false (check-port -1))
  (check-false (check-port "8080")))

(let ([check-non-empty (validator-check (validator-row-by-name 'nonEmpty))])
  (check-true (check-non-empty "a"))
  (check-true (check-non-empty " "))
  (check-false (check-non-empty ""))
  (check-false (check-non-empty 1)))

;; RFN-001: 表に無い命題名は引けない。
(check-false (validator-row-by-name 'validHost))
(check-false (validator-row-by-oid 'o-valid-host))
(check-false (validator-row-by-proposition '(Prop ValidHost)))

;; RFN-001: 導入と射影の primitive は判定表を過不足なく覆う。
(check-equal? (map second introduction-table) '(untrustedInt untrustedString))
(check-equal? (map second projection-table)
              '(unrefinePort unrefineNonEmpty))
(check-equal? (third (introduction-row-by-name 'untrustedInt)) 'Int)
(check-equal? (third (projection-row-by-name 'unrefinePort))
              '(Prop ValidPort))
(check-equal? (fourth (projection-row-by-name 'unrefinePort)) 'Int)
(check-false (introduction-row-by-name 'unrefinePort))
(check-false (projection-row-by-name 'untrustedInt))

(test-case "projection coverage compares (proposition type) pairs"
  ;; validator 行と projection 行は命題と型の両方で一致していなければならない。
  (check-equal?
   (map (lambda (v)
          (list (validator-proposition v) (validator-payload-type v)))
        validator-table)
   (map (lambda (p) (list (third p) (fourth p)))
        projection-table)))

;; RFN-001: カーネル primitive 名は G2d が足した 6 個だけである。
(for ([name (in-list '(validPort nonEmpty untrustedInt untrustedString
                       unrefinePort unrefineNonEmpty))])
  (check-true (kernel-primitive-name? name) (format "~a" name)))
(check-false (kernel-primitive-name? 'add))
(check-false (kernel-primitive-name? 'acquire))

;; RFN-001: 失敗側メッセージは nm から決定的に構成する。
(check-equal? (validator-error-message 'validPort) "validPort: rejected")
(check-equal? (validator-error-message 'validPort)
              (validator-error-message 'validPort))

;; RFN-001: Owned-free 制限は Owned を部分に含む型をすべて落とす。
(check-true (owned-free? 'Int))
(check-true (owned-free? '(Record ((a Int imm) (b (List String) imm)))))
(check-true (owned-free? '(Refined Int (Prop ValidPort))))
(check-false (owned-free? '(Owned Res)))
(check-false (owned-free? '(List (Owned Res))))
(check-false (owned-free? '(Option (Owned Res))))
(check-false (owned-free? '(Result Int (Owned Res))))
(check-false (owned-free? '(Record ((a (Owned Res) imm)))))
(check-false (owned-free? '(Untrusted (Owned Res))))
(check-false (owned-free? '(Refined (Owned Res) (Prop ValidPort))))
(check-false (owned-free? '(NFn (Int) (Owned Res) () ())))
(check-false (owned-free? '(NFn ((Owned Res)) Int () ())))
(check-false (owned-free? '(NFn () Unit ((Yield (Owned Res))) ())))
(check-true (owned-free? '(NFn () Unit (Suspend) ())))

;; RFN-001: リテラル型はペイロード束縛検査が使う判定である。
(check-equal? (literal-type 8080) 'Int)
(check-equal? (literal-type "localhost") 'String)
(check-equal? (literal-type 'unit) 'Unit)
(check-false (literal-type '(UVal 1)))
