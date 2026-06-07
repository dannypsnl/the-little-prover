#lang racket/base
(require rackunit "../j-bob.rkt")

;; chapter1.example1
(check-equal?
  (J-Bob/step (prelude)
              '(car (cons 'ham '(eggs)))
              '(((1) (cons 'ham '(eggs)))
                (() (car '(ham eggs)))))
  ''ham)

;; chapter1.example4: rewriting with an axiom
(check-equal?
  (J-Bob/step (prelude)
              '(atom (cons a b))
              '((() (atom/cons a b))))
  ''nil)

;; a step that doesn't apply leaves the term unchanged (J-Bob's behavior)
(check-equal?
  (J-Bob/step (prelude)
              '(atom (cons a b))
              '((() (car/cons a b))))
  '(atom (cons a b)))

;; J-Bob/define: non-recursive defun with trivial totality (seed nil)
(define defs+pair
  (J-Bob/define (prelude)
                '(((defun pair (x y) (cons x (cons y '()))) nil))))
(check-equal? (car (reverse defs+pair))
              '(defun pair (x y) (cons x (cons y '()))))
(check-equal? (length defs+pair) (+ 1 (length (prelude))))

;; J-Bob/define rejects a bad proof: returns defs unchanged
(check-equal?
  (J-Bob/define (prelude)
                '(((dethm nonsense (x) (equal x 'fred)) nil)))
  (prelude))
