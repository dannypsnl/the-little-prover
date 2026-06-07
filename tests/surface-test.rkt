#lang racket/base
(require rackunit shrubbery/parse "../private/surface.rkt")

;; helper: parse a one-line shrubbery term and lower it
(define (t str)
  (define in (open-input-string str))
  (port-count-lines! in)
  (define stx (parse-all in)) ; (multi (group …))
  (parse-group-term (cadr (syntax->datum stx)) #f))

(check-equal? (t "x") 'x)
(check-equal? (t "cons(x, y)") '(cons x y))
(check-equal? (t "cons(x, cons(y, '[]'))") '(cons x (cons y '())))
(check-equal? (t "'t'") ''t)
(check-equal? (t "'nil'") ''nil)
(check-equal? (t "'?'") ''?)
(check-equal? (t "'[1, 2]'") ''(1 2))
(check-equal? (t "'[ham, eggs]'") ''(ham eggs))
(check-equal? (t "0") ''0)
(check-equal? (t "x == y") '(equal x y))
(check-equal? (t "1 + 2") '(+ '1 '2))
(check-equal? (t "size(cdr(xs)) < size(xs)") '(< (size (cdr xs)) (size xs)))
(check-equal? (t "(x == y) == 't'") '(equal (equal x y) 't))
(check-equal? (t "if(atom(x), 't', 'nil')") '(if (atom x) 't 'nil))
;; axiom-name mapping applies to application heads
(check-equal? (t "car_cons(a, b)") '(car/cons a b))
(check-equal? (t "natp_size(x)") '(natp/size x))
(check-equal? (t "memb_remb0()") '(memb_remb0)) ; user names pass through
;; chained infix without parens is rejected
(check-exn exn:fail:syntax? (lambda () (t "a + b + c")))

;; ---------- whole programs ----------
(define (prog str)
  (define in (open-input-string str))
  (port-count-lines! in)
  (parse-program (parse-all in)))

(define basics "
defun pair(x, y):
  cons(x, cons(y, '[]'))

dethm first_of_pair(a, b):
  equal(car(pair(a, b)), a)
proof:
  at [1, 1]: pair(a, b)
  at [1]: car_cons(a, cons(b, '[]'))
  at []: equal_same(a)
")

(define es (prog basics))
(check-equal? (length es) 2)
(check-equal? (entry-def (car es)) '(defun pair (x y) (cons x (cons y '()))))
(check-equal? (entry-seed (car es)) 'nil)
(check-equal? (entry-steps (car es)) '())
(check-equal? (entry-def (cadr es))
              '(dethm first_of_pair (a b) (equal (car (pair a b)) a)))
(check-equal? (entry-steps (cadr es))
              '(((1 1) (pair a b))
                ((1) (car/cons a (cons b '())))
                (() (equal-same a))))
;; per-step srclocs captured
(check-equal? (length (entry-step-stxs (cadr es))) 3)
(check-true (syntax? (car (entry-step-stxs (cadr es)))))

;; measure + block-if body + totality proof
(define remb "
defun remb(xs):
  measure: size(xs)
  if atom(xs):
    '[]'
  else if equal(car(xs), '?'):
    remb(cdr(xs))
  else:
    cons(car(xs), remb(cdr(xs)))
proof:
  at [Q]: natp_size(xs)
  at []: if_true(if(atom(xs), 't', size(cdr(xs)) < size(xs)), 'nil')
  at [E]: size_cdr(xs)
  at []: if_same(atom(xs), 't')
")
(define rembe (car (prog remb)))
(check-equal? (entry-def rembe)
              '(defun remb (xs)
                      (if (atom xs)
                          '()
                          (if (equal (car xs) '?)
                              (remb (cdr xs))
                              (cons (car xs) (remb (cdr xs)))))))
(check-equal? (entry-seed rembe) '(size xs))
(check-equal? (length (entry-steps rembe)) 4)

;; induction seed
(define ind "
dethm trivial(xs):
  equal(xs, xs)
proof induction(list_induction(xs)):
  at []: equal_same(xs)
")
(check-equal? (entry-seed (car (prog ind))) '(list-induction xs))

;; errors
(check-exn exn:fail:syntax? ; proof with no preceding definition
           (lambda () (prog "proof:\n  at []: equal_same(a)\n")))
(check-exn exn:fail:syntax? ; dethm without proof
           (lambda () (prog "dethm t1(a):\n  equal(a, a)\n")))
(check-exn exn:fail:syntax? ; measure but no totality proof
           (lambda () (prog "defun f(x):\n  measure: size(x)\n  if atom(x):\n    'nil'\n  else:\n    f(cdr(x))\n")))
(check-exn exn:fail:syntax? ; if without else
           (lambda () (prog "defun g(x):\n  if atom(x):\n    'nil'\n")))

;; ---------- sorry ----------
;; a bare `sorry` step parses to the marker 'sorry
(define sorried "
dethm t2(a):
  equal(a, a)
proof:
  sorry
")
(check-equal? (entry-steps (car (prog sorried))) '(sorry))
;; mixed: real steps before the sorry
(define sorried2 "
defun pair2(x, y):
  cons(x, cons(y, '[]'))

dethm first2(a, b):
  equal(car(pair2(a, b)), a)
proof:
  pair2(a, b)
  sorry
")
(check-equal? (entry-steps (cadr (prog sorried2)))
              '((within () (pair2 a b)) sorry))
