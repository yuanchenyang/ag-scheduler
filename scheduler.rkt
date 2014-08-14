#lang s-exp rosette/safe

(require rosette/lib/meta/meta
         rosette/lib/reflect/match)

(struct node (item left right)
        #:transparent)

(define nil #f)
(define nil? false?)

(define-synthax (tree low high #:depth k)
  #:assert (>= k 0)
  [choose nil (node [choose-number low high]
                    (tree low high #:depth (- k 1))
                    (tree low high #:depth (- k 1)))])

(define (sum-tree tree)
  (match tree
    [(? nil?) 0]
    [(node i l r) (+ i (sum-tree l) (sum-tree r))]))

(define t (tree 1 3 #:depth 3))

(time
 (solve/evaluate
   (begin (assert (= (sum-tree t) 10))
          t)))
