#lang racket

(require rackunit
         "../compat.rkt"
         "../region.rkt"
         "../region-param.rkt"
         "../type-equiv.rkt")

;; spec §8。VAR-004 の共変と不変。
;; 具体的な region の番号は大域の採番に依るため、literal を書かず
;; region-at と region->rho から取る。
(define skeleton '(Scope () (Scope () 0)))
(define ir (build-region-ir skeleton))
(define outer (region->rho ir (region-at ir '())))
(define inner (region->rho ir (region-at ir '(0 0))))

;; 束縛の表は使わない。具体的な region どうしの包含だけを見る。
(define relation (make-region-relation ir '(Scope () 0)))

;; §8.1。長く生きる借用は短く生きる借用の位置へ渡せる。
(test-case
 "共有借用の region は共変である"
 (check-not-equal? outer inner)
 (check-true (compat? `(Borrowed Int ,outer) `(Borrowed Int ,inner)
                      '() relation)))

;; 逆向きは認めない。短く生きる借用を長く生きる位置へ渡すと、
;; 借用の所有者が退場したあとで使える。
(test-case
 "短く生きる共有借用は長く生きる位置へ渡せない"
 (check-false (compat? `(Borrowed Int ,inner) `(Borrowed Int ,outer)
                       '() relation)))

;; §8.1 の第 2 項。構成子をまたぐ変換はどちらの向きも認めない。
(test-case
 "Borrowed と BorrowedMut のあいだは変換しない"
 (check-false (compat? `(BorrowedMut Int ,outer) `(Borrowed Int ,outer)
                       '() relation))
 (check-false (compat? `(Borrowed Int ,outer) `(BorrowedMut Int ,outer)
                       '() relation)))

;; §8.2。可変借用の region 欄は一致を要求し続ける。
(test-case
 "可変借用の region は不変である"
 (check-true (compat? `(BorrowedMut Int ,outer) `(BorrowedMut Int ,outer)
                      '() relation))
 (check-false (compat? `(BorrowedMut Int ,outer) `(BorrowedMut Int ,inner)
                       '() relation))
 (check-false (compat? `(BorrowedMut Int ,inner) `(BorrowedMut Int ,outer)
                       '() relation)))

;; §8.1 の末尾。payload の判定へ関係の文脈が届く。
;; 届かないと最上位でだけ共変になり、1 段下で equal? に戻る。
(test-case
 "共有借用の payload へ関係の文脈が届く"
 (check-true (compat? `(Borrowed (Borrowed Int ,outer) ,outer)
                      `(Borrowed (Borrowed Int ,inner) ,inner)
                      '() relation)))

;; §8.2。可変借用の payload は type-equiv? で判定する。
;; 書き込みの経路であり、payload の型が広がると、書き込んだ値が
;; 元の場所の型に合わなくなる。
(test-case
 "可変借用の payload は幅を広げない"
 (define wide '(Record ((a Int imm) (b Int imm))))
 (define narrow '(Record ((a Int imm))))
 (check-true (compat? wide narrow '() relation))
 (check-false (compat? `(BorrowedMut ,wide ,outer)
                       `(BorrowedMut ,narrow ,outer)
                       '() relation)))

;; §8.4。type-equiv? は緩めない。
;; 同値と互換を同じ関係にすると、policy-narrative.md §6.2 の契約、
;; つまり同値な二型は互換である、が意味を持たなくなる。
(test-case
 "type-equiv? の借用の region は equal? のままである"
 (check-false (type-equiv? `(Borrowed Int ,outer) `(Borrowed Int ,inner)))
 (check-true (type-equiv? `(Borrowed Int ,outer) `(Borrowed Int ,outer))))

;; §6.2。既定の関係のままなら判定は変わらない。
(test-case
 "既定の関係では region の一致を要求する"
 (check-false (compat? `(Borrowed Int ,outer) `(Borrowed Int ,inner)))
 (check-true (compat? `(Borrowed Int ,outer) `(Borrowed Int ,outer))))

;; §8.3。imm の field は payload の判定へ関係の文脈を渡す。
;; field の型の中の共有借用も共変になる。
(test-case
 "imm field の中の共有借用は共変である"
 (check-true (compat? `(Record ((a (Borrowed Int ,outer) imm)))
                      `(Record ((a (Borrowed Int ,inner) imm)))
                      '() relation))
 (check-false (compat? `(Record ((a (Borrowed Int ,inner) imm)))
                       `(Record ((a (Borrowed Int ,outer) imm)))
                       '() relation)))

;; §8.3。mut の field は型同値を保ち、region も不変である。
;; 共変にすると、field へ書き込んだ値の region が宣言より短くなりうる。
(test-case
 "mut field の中の共有借用は不変である"
 (check-true (compat? `(Record ((a (Borrowed Int ,outer) mut)))
                      `(Record ((a (Borrowed Int ,outer) mut)))
                      '() relation))
 (check-false (compat? `(Record ((a (Borrowed Int ,outer) mut)))
                       `(Record ((a (Borrowed Int ,inner) mut)))
                       '() relation)))

;; §6.3。分岐の再照合も同じ関係を見る。merge-branch-compatible? の imm の
;; 節は type-compatible? を呼び、type-compatible? は current-region-relation
;; から関係を取る。parameter を経由するため、経路の途中で関係が落ちない。
(test-case
 "分岐の再照合は parameter の関係を見る"
 (parameterize ([current-region-relation relation])
   (check-true ((current-region-relation) outer inner))
   (check-false ((current-region-relation) inner outer))))
