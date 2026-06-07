#lang racket/base
(require rackunit "../examples/basics.rkt"
         (prefix-in memb: "../examples/memb.rkt")
         (prefix-in arith: "../examples/arith.rkt"))

(check-equal? proved-names '(pair second_of first_of_pair second_of_pair))
(check-equal? (length defs) (+ 4 23)) ; 4 ours + 23 in (prelude)
(check-pred list? defs)

;; A wrong proof step must be a syntax error AT THAT STEP (line 8).
(define bad-program
  (string-append
    "#lang the-little-prover\n" ; line 1
    "defun pair(x, y):\n" ; line 2
    "  cons(x, cons(y, '[]'))\n" ; line 3
    "dethm broken(a, b):\n" ; line 4
    "  equal(car(cons(a, b)), b)\n" ; line 5
    "proof:\n" ; line 6
    "  at [1]: car_cons(a, b)\n" ; line 7 (applies)
    "  at []: equal_same(a)\n")) ; line 8 (does not apply)

(define err
  (with-handlers ([exn:fail:syntax? values])
    (define in (open-input-string bad-program))
    (port-count-lines! in)
    (parameterize ([read-accept-reader #t]
                   [current-namespace (make-base-namespace)])
      (eval (read-syntax 'bad in)))
    (fail "expected a syntax error")))
(check-regexp-match #rx"does not apply" (exn-message err))
(check-regexp-match #rx"current claim: equal\\(a, b\\)" (exn-message err))
(check-equal? (syntax-line (car (exn:fail:syntax-exprs err))) 8)

;; induction example (the book's memb?/remb)
(check-equal? memb:proved-names '(memb remb memb_remb))

;; infix sugar + conditional claim
(check-equal? arith:proved-names '(plus_swap zero_plus))

;; A `sorry` is a syntax error AT THAT STEP showing the claim there.
(define sorried-program
  (string-append
    "#lang the-little-prover\n" ; line 1
    "defun pair(x, y):\n" ; line 2
    "  cons(x, cons(y, '[]'))\n" ; line 3
    "dethm first_of_pair(a, b):\n" ; line 4
    "  equal(car(pair(a, b)), a)\n" ; line 5
    "proof:\n" ; line 6
    "  sorry\n")) ; line 7
(define sorry-err
  (with-handlers ([exn:fail:syntax? values])
    (define in (open-input-string sorried-program))
    (port-count-lines! in)
    (parameterize ([read-accept-reader #t]
                   [current-namespace (make-base-namespace)])
      (eval (read-syntax 'sorried in)))
    (fail "expected a syntax error")))
(check-regexp-match #rx"sorry" (exn-message sorry-err))
(check-regexp-match #rx"current claim: equal\\(car\\(pair\\(a, b\\)\\), a\\)"
                    (exn-message sorry-err))
(check-equal? (syntax-line (car (exn:fail:syntax-exprs sorry-err))) 7)
