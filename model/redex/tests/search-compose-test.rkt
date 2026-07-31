#lang racket/base

(require racket/list
         rackunit
         "../traits.rkt")

(test-case "TRT-004: 正典の intersect-table は非巡回である"
  (check-true (intersect-acyclic?)))

(test-case "TRT-004: 巡回する intersect fixture は拒否される"
  ;; 自己ループ。出力 trait が自分の成分に現れる。
  (check-false
   (intersect-acyclic? (list (list 'o-z 'z-name 'A 'B 'A))))
  ;; 2 行をまたぐ巡回。C は A から作られ、A は C から作られる。
  (check-false
   (intersect-acyclic? (list (list 'o-x 'x-name 'A 'B 'C)
                             (list 'o-y 'y-name 'C 'D 'A)))))

(test-case "TRT-004: 成分を共有するだけの表は巡回ではない"
  ;; 同じ trait が複数の行の成分に現れても、辺をたどって戻らなければよい。
  (check-true
   (intersect-acyclic? (list (list 'o-p 'p-name 'A 'B 'AB)
                             (list 'o-q 'q-name 'A 'C 'AC)))))
