#lang s-exp rosette

(require rosette/lib/meta/meta
         rosette/lib/reflect/match)

(define red 0)
(define black 1)

(struct node (color key left right)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (fprintf port "(node ~a ~a ~a ~a)"
              (if (= (node-color self) red) 'red 'black)
              (node-key self)
              (node-left self)
              (node-right self)))])

(define nil #f)
(define nil? false?)

(define (size tree)
  (match tree
    [(? nil?) 0]
    [(node _ _ l r) (+ 1 (size l) (size r))]))

(define (compare-all tree op key)
  (match tree
    [(? nil?) #t]
    [(node _ k l r)
     (and (op k key)
          (compare-all l op key)
          (compare-all r op key))]))

(define (ordered-keys? tree)
  (match tree
    [(? nil?) #t]
    [(node _ k l r)
     (and (compare-all l < k)
          (ordered-keys? l)
          (compare-all r > k)
          (ordered-keys? r))]))

(define (color tree)
  (match tree
   [(? nil?) black]
   [(node c _ _ _) c]))

(define (all-paths-have-same-number-of-black-nodes? tree)
  (match tree
    [(? nil?) black]
    [(node c _ l r)
     (let ([pl (all-paths-have-same-number-of-black-nodes? l)]
           [pr (all-paths-have-same-number-of-black-nodes? r)])
       (and pl pr (= pl pr) (+ c pl)))]))

(define (red-nodes-have-black-children? tree)
  (match tree
    [(? nil?) #t]
    [(node c _ l r)
     (and (red-nodes-have-black-children? l)
          (red-nodes-have-black-children? r)
          (or (= c black)
              (and (= (color l) black)
                   (= (color r) black))))]))

(define (red-black-tree? tree)
  (and (ordered-keys? tree)
       (= (color tree) black)
       (red-nodes-have-black-children? tree)
       (all-paths-have-same-number-of-black-nodes? tree)
       #t))

(define-synthax (tree low high #:depth k)
  #:assert (>= k 0)
  [choose nil (node [choose red black]
                    [choose-number low high]
                    (tree low high #:depth (- k 1))
                    (tree low high #:depth (- k 1)))])

(define (angelic-tree low high #:depth k)
  (assert (>= k 0))
  (local ([define-symbolic* choice boolean?])
    (if choice
        nil
        (local ([define-symbolic* red? boolean?]
                [define-symbolic* key number?])
          (assert (>= key low))
          (assert (<= key high))
          (node (if red? red black) key
                (angelic-tree low high #:depth (- k 1))
                (angelic-tree low high #:depth (- k 1)))))))

(define t (angelic-tree 0 7 #:depth 3))
(time
 (solve/evaluate
  (begin (assert (red-black-tree? t))
         (assert (= (size t) 5))
         t)))
