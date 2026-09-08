#lang racket

(require rackunit
         "../region.rkt")

;; unsafe.md §4.4。子の並びは項の書き順に従う。
(test-case "core-children の子の並び（unsafe.md §4.4）"
  (check-equal? (core-children '(AddressOf x)) '(x))
  (check-equal? (core-children '(RawLoad x)) '(x))
  (check-equal? (core-children '(Unsafe x)) '(x))
  (check-equal? (core-children '(PtrOffset x 1)) '(x 1))
  (check-equal? (core-children '(RawStore x 1)) '(x 1))
  ;; FromRawPtr の ρ は Core の子ではない。
  (check-equal? (core-children '(FromRawPtr x 0)) '(x))
  (check-equal? (core-children '(FromRawPtr x (RParam rp))) '(x))
  (check-equal? (core-children '(PtrVal 0 () Mut (Prov owned))) '()))

;; core-children と core-with-children が 1 対 1 で対応する。
(test-case "core-with-children の再構成（unsafe.md §4.4）"
  (for ([term (in-list '((AddressOf x)
                         (RawLoad x)
                         (Unsafe x)
                         (PtrOffset x 1)
                         (RawStore x 1)
                         (FromRawPtr x 0)
                         (FromRawPtr x (RParam rp))
                         (PtrVal 0 () Mut (Prov owned))))])
    (check-equal? (core-with-children term (core-children term)) term
                  (format "恒等: ~s" term)))
  ;; 子を差し替えると据え置きの成分が保たれる。
  (check-equal? (core-with-children '(FromRawPtr x (RParam rp)) '(y))
                '(FromRawPtr y (RParam rp)))
  (check-equal? (core-with-children '(PtrOffset x 1) '(y 2))
                '(PtrOffset y 2))
  (check-equal? (core-with-children '(RawStore x 1) '(y 2))
                '(RawStore y 2))
  (check-equal? (core-with-children '(Unsafe x) '(y)) '(Unsafe y)))

;; region IR は新しい形の内側の項へも届く。
(test-case "region IR が Unsafe の内側へ届く（unsafe.md §4.4）"
  (define core '(Unsafe (RawStore (AddressOf x) 1)))
  (check-equal? (core-points core)
                '(() (0) (0 0) (0 0 0) (0 1)))
  (define ir (build-region-ir core))
  (check-true (region-ir-ok? ir core)))

;; FromRawPtr の ρ は RegionApp と同じ直接の寿命引数として扱う。
(test-case "FromRawPtr の concrete region と RVar（unsafe.md §5.4）"
  (define concrete-core '(RegionLam (rp) (FromRawPtr x 0)))
  (define concrete-ir (build-region-ir concrete-core))
  (define concrete-rel (make-region-relation concrete-ir concrete-core))
  (check-true (concrete-rel '(RParam rp) 0))

  (define param-core '(RegionLam (rp) (FromRawPtr x (RParam rp))))
  (define param-ir (build-region-ir param-core))
  (define param-rel (make-region-relation param-ir param-core))
  (check-false (param-rel '(RParam rp) 0))

  (define direct-core '(FromRawPtr x (RVar 0)))
  (define direct-ir (build-region-ir direct-core))
  (define resolved-rho
    (region->rho direct-ir (region-at direct-ir '())))
  (check-equal?
   (materialize-regions direct-ir direct-core (hash 0 '(RVar 0))
                        (hash 0 (region-at direct-ir '())))
   `(FromRawPtr x ,resolved-rho)))
