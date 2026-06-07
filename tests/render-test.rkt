#lang racket/base
(require rackunit "../private/render.rkt")

(check-equal? (term->surface 'x) "x")
(check-equal? (term->surface ''t) "'t'")
(check-equal? (term->surface ''()) "'[]'")
(check-equal? (term->surface ''(1 2)) "'[1, 2]'")
(check-equal? (term->surface '(cons x (cons y '()))) "cons(x, cons(y, '[]'))")
(check-equal? (term->surface '(if (atom x) 't 'nil)) "if(atom(x), 't', 'nil')")
(check-equal? (term->surface '(car/cons a b)) "car_cons(a, b)")
(check-equal? (term->surface '(< (size (cdr xs)) (size xs)))
              "<(size(cdr(xs)), size(xs))")
