#lang racket/base
;; Racket port of vendor/j-bob-lang.scm — the tiny host language J-Bob is
;; written in. Total car/cdr/equal/+/</natp over S-expressions, booleans
;; 't/'nil, if that treats any non-'nil as true, defun/dethm as define.
;;
;; Also usable as a module language (#lang s-exp …) so that j-bob.scm and
;; little-prover.scm can be `include`d verbatim with these names shadowing
;; racket/base.

(provide (except-out (all-from-out racket/base) if car cdr + <)
         (rename-out [j-if if] [j-car car] [j-cdr cdr] [j-+ +] [j-< <])
         equal atom natp size defun dethm)

(define (num x) (if (number? x) x 0))
(define (atom x) (if (pair? x) 'nil 't))
(define (j-car x) (if (pair? x) (car x) '()))
(define (j-cdr x) (if (pair? x) (cdr x) '()))
(define (equal x y) (if (equal? x y) 't 'nil))
(define (natp x) (if (integer? x) (if (< x 0) 'nil 't) 'nil))
(define (j-+ x y) (+ (num x) (num y)))
(define (j-< x y) (if (< (num x) (num y)) 't 'nil))

(define-syntax-rule (j-if Q A E)
  (if (equal? Q 'nil) E A))

(define-syntax-rule (defun name (arg ...) body)
  (define (name arg ...) body))
(define-syntax-rule (dethm name (arg ...) body)
  (define (name arg ...) body))

(define (size x)
  (j-if (atom x)
        0
        (j-+ 1 (j-+ (size (j-car x)) (size (j-cdr x))))))
