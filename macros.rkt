;; Sandbox for testing macros

#lang s-exp rosette/safe

(require rosette/lib/meta/meta)

(define-synthax (list-from (attrs ...) #:depth d)
  #:assert (>= d 0)
  (choose '() (cons (quote (attrs ...))
                    (list-from (attrs ...) #:depth (- d 1)))))

;(list-from ('a ) #:depth 2)

(define-syntax-rule (choose-list attrs)
  (choose . attrs))

(define-syntax-rule (test attrs)
  (+ . attrs))

;; (let ([attrs '(a b c d)])
;;   (choose-list attrs))

(define (testfn a [b (length a)])
  (displayln a)
  (displayln b))

(testfn '(1 2 3 4))
