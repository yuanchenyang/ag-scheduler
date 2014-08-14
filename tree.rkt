#lang s-exp rosette/safe

(require rosette/lib/meta/meta)

; We represent tree using nested lists.  Each node is a
; list consisting of a unique integer id, a list of attribute/value pairs
; and  a possibly empty list of child nodes.  Ids in a well-formed tree
; must cover a prefix of the natural numbers.

(define node-type       car)
(define node-class      cadr)
(define node-attributes caddr)
(define node-children   cadddr)

(define (get-attribute n att) (unbox (cdr (assoc att (node-attributes n)))))
(define (get-child n child)
  (if (null? child)
      n
      (assoc child (node-children n))))

(define (set-attribute! n att val)
  (map (lambda (p) (if (equal? att (car p))
                       (set-box! (cdr p) val)
                       (void)))
       (node-attributes n))
  (void))

(define assign-class car)
(define assign-base  cadr)
(define assign-name  caddr)

(define (eg-attrs) `[(a . ,(box #f)) (b . ,(box #f))])

(define (eg-leaf1) `(left leaf ,(eg-attrs) []))

(define (eg-leaf2) `(right leaf ,(eg-attrs) []))

;;(define-syntax-rule (gen-attrs attrs ...)


(define-syntax-rule (leaf name)
  `(name leaf ,(eg-attrs) []))

(define-syntax-rule (midnode name child1 child2)
  `(name midnode ,(eg-attrs) [,child1 ,child2]))

(define-syntax-rule (root name child)
  `(name root [] [,child]))

;;(define (eg-midnode)
;;  `(child midnode
;;          ,(eg-attrs)
;;          [,(eg-leaf1) ,(eg-leaf2)]))
;;
;;(define (eg-tree)
;;  `(top root
;;        []
;;        [,(eg-midnode)]))

(define (eg-tree)
  (root top (midnode child
                     (leaf left)
                     (leaf right))))

(define eg-deps
  '([(root child a)    (root child b)]
    [(midnode left a)  (midnode () a)]
    [(midnode right a) (midnode () a)]
    [(midnode () b)    (midnode left b) (midnode right b)]
    [(leaf () b)]))

(define eg-schedule
  '([BU (leaf () b)
        (midnode () b)]
    [TD (root child a)
        (midnode left a)
        (midnode right a)]))

;;
(define eg-invalid-schedule
  '((BU (midnode () b)
        (root child a)
        (leaf () b))
    (BU (midnode left a)
        (midnode right a))))

(define (check-td assigns tree)
  (unless (null? tree)
    (check-assigns assigns tree)
    (map (lambda (child) (check-td assigns child))
         (node-children tree))))

(define (check-bu assigns tree)
  (unless (null? tree)
    (map (lambda (child) (check-bu assigns child))
         (node-children tree))
    (check-assigns assigns tree)))

(define (check-assigns assigns tree)
  (let ([cur-assigns (filter (lambda (assign)
                               (equal? (assign-class assign)
                                       (node-class tree)))
                             assigns)])
    ;(displayln cur-assigns)
    ;(displayln tree)
    (map (lambda (assign)
           (assert (not (attr-value tree assign))) ; Single assignment
           (check-deps assign tree)
           (set-attribute! (get-child tree (assign-base assign))
                           (assign-name assign)
                           #t))
         cur-assigns)))

(define (check-deps assign tree)
  (unless (equal? assign '(leaf () no-op))
    (map (lambda (dep)
           (assert (attr-value tree dep)))
         (cdr (assoc assign eg-deps)))))

(define (attr-value tree attr)
  (get-attribute (get-child tree
                            (assign-base attr))
                 (assign-name attr)))

(define (check-schedule sched tree)
  (map (lambda (traversal)
         (let ([type    (car traversal)]
               [assigns (cdr traversal)])
           (cond [(equal? type 'TD) (check-td assigns tree)]
                 [(equal? type 'BU) (check-bu assigns tree)])))
       sched)
  tree)

(define (fully-assigned tree)
  (unless (null? tree)
    (map (lambda (attr)
           (assert (unbox (cdr attr))))
         (node-attributes tree))
    (map fully-assigned
         (node-children tree))
    (void)))

(define-synthax (synth-schedule (attrs ...) #:depth d)
  #:assert (>= d 0)
  [choose '() (cons (cons [choose 'TD 'BU]
                          (schedule-assign (attrs ...) #:depth 3))
                    (synth-schedule (attrs ...) #:depth (- d 1)))])

(define-synthax (schedule-assign (attrs ...) #:depth d)
  #:assert (>= d 0)
  [choose '() (cons [choose attrs ...]
                    (schedule-assign (attrs ...) #:depth (- d 1)))])


;; Attempt to generate a schedule sketch without using macros. Not working right
;; now because these functions run in an (infinite?) loop when called
(define (make-sketch low high alow ahigh alen attrs)
  (define (attrs-helper n)
    (assert >= n 0)
    (if (= n 0) '()
        (local ([define-symbolic* index number?])
          (assert (>= index 0))
          (assert (<= index alen))
          (cons (list-ref attrs index)
                (attrs-helper (- n 1))))))
  (define (traversal-helper n)
    (assert >= n 0)
    (if (= n 0) '()
        (local ([define-symbolic* numattrs number?]
                [define-symbolic* td?      boolean?])
          (assert (>= numattrs low))
          (assert (<= numattrs high))
          (cons (cons (if td? 'TD 'BU)
                      (attrs-helper numattrs))
                (traversal-helper (- n 1))))))
  (traversal-helper (choose-number low high)))

;;(define sketch
;;  (make-sketch 1 2 2 3 5 '((root child a)
;;                           (midnode left a)
;;                           (midnode right a)
;;                           (midnode () b)
;;                           (leaf () b))))


;; Synthesizing a tree
(define-synthax (synth-tree name #:depth k)
  #:assert (>= k 0)
  [choose (leaf name)
          (midnode name
                   (synth-tree left  #:depth (- k 1))
                   (synth-tree right #:depth (- k 1)))])

(define t (root top (synth-tree child #:depth 2)))
(define model (verify (check-schedule eg-schedule t)))
(evaluate t model)

;; Schedule sketch generated using macros
;;(define sketch (synth-schedule ('(root child a)
;;                                '(midnode left a)
;;                                '(midnode right a)
;;                                '(midnode () b)
;;                                '(leaf () b)
;;                                ;'(leaf () no-op))
;;                                )
;;                               #:depth 2))
;;
;;(time (solve/evaluate
;;       (begin
;;         (define a
;;           (root top (midnode child
;;                              (leaf left)
;;                              (leaf right))))
;;         (check-schedule sketch
;;                         a)
;;         (fully-assigned a)
;;         sketch)))

;; (define-synthax (schedule (attrs ...))
;;   `([,(choose 'TD 'BU)
;;      ,(choose attrs ...)
;;      ,(choose attrs ...)
;;      ]
;;     [,(choose 'TD 'BU)
;;      ,(choose attrs ...)
;;      ,(choose attrs ...)
;;      ,(choose attrs ...)
;;      ]))

;;(define model
;;  (solve (check-schedule sketch
;;                         (eg-tree))))
;;(evaluate sketch model)
