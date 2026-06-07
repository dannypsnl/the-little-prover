#lang racket/base
(require rackunit "../private/core.rkt" "../private/check.rkt")

(define P (prelude))
(define pair-def '(defun pair (x y) (cons x (cons y '()))))
(define (ent def seed steps) (entry def seed steps #f (map (lambda (s) #f) steps)))
(define (run-check defs entries)
  (define-values (new-defs _states) (check-program defs entries))
  new-defs)

;; non-recursive defun, no steps
(define defs1 (run-check P (list (ent pair-def 'nil '()))))
(check-equal? (car (reverse defs1)) pair-def)

;; a dethm with the book's proof
(define fop
  (ent '(dethm first-of-pair (a b) (equal (car (pair a b)) a))
       'nil
       '(((1 1) (pair a b))
         ((1) (car/cons a (cons b '())))
         (() (equal-same a)))))
(check-not-exn (lambda () (run-check defs1 (list fop))))

;; step states are returned alongside defs
(define-values (defs-fop states-fop)
  (check-program defs1 (list fop)))
(check-equal? (length states-fop) 3)
(check-equal? (cadr (car states-fop)) ; before first step
              '(equal (car (pair a b)) a))

;; failing step reports which one
(define bad
  (ent '(dethm broken (a b) (equal (car (cons a b)) b))
       'nil
       '(((1) (car/cons a b))
         (() (equal-same a)))))
(define f
  (with-handlers ([check-failure? values])
    (run-check P (list bad))
    (fail "expected a check-failure")))
(check-regexp-match #rx"does not apply" (check-failure-message f))
(check-equal? (check-failure-claim f) '(equal a b))

;; ill-formed step: unknown rule name
(define unknown
  (ent '(dethm broken2 (a) (equal a a))
       'nil
       '((() (no-such-rule a)))))
(check-regexp-match
  #rx"ill-formed step"
  (check-failure-message
    (with-handlers ([check-failure? values])
      (run-check P (list unknown))
      (fail "expected a check-failure"))))

;; proof that stops too early
(define early
  (ent '(dethm broken3 (a b) (equal (car (cons a b)) a))
       'nil
       '(((1) (car/cons a b)))))
(check-regexp-match
  #rx"claim is not yet 't"
  (check-failure-message
    (with-handlers ([check-failure? values])
      (run-check P (list early))
      (fail "expected a check-failure"))))

;; ill-formed definition (unbound variable in body)
(check-regexp-match
  #rx"ill-formed definition"
  (check-failure-message
    (with-handlers ([check-failure? values])
      (run-check P (list (ent '(defun oops (x) (cons x y)) 'nil '())))
      (fail "expected a check-failure"))))

;; ---------- sorry ----------
;; a sorry reports the claim at that point in the proof
(define sorried
  (ent '(dethm first-of-pair2 (a b) (equal (car (pair a b)) a))
       'nil
       (list '((1 1) (pair a b)) 'sorry)))
(define hf
  (with-handlers ([check-failure? values])
    (run-check defs1 (list sorried))
    (fail "expected a check-failure")))
(check-regexp-match #rx"sorry" (check-failure-message hf))
(check-equal? (check-failure-claim hf)
              '(equal (car (cons a (cons b '()))) a))

;; a sorry as the only step reports the initial claim
(define sorried0
  (ent '(dethm trivial2 (a) (equal a a)) 'nil (list 'sorry)))
(define hf0
  (with-handlers ([check-failure? values])
    (run-check P (list sorried0))
    (fail "expected a check-failure")))
(check-regexp-match #rx"sorry" (check-failure-message hf0))
(check-equal? (check-failure-claim hf0) '(equal a a))

;; a sorry after a complete proof says to delete it
(define sorried-done
  (ent '(dethm trivial3 (a) (equal a a))
       'nil
       (list '(() (equal-same a)) 'sorry)))
(define hfd
  (with-handlers ([check-failure? values])
    (run-check P (list sorried-done))
    (fail "expected a check-failure")))
(check-regexp-match #rx"delete" (check-failure-message hfd))
