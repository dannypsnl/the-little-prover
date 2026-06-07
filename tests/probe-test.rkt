#lang racket/base
(require rackunit json racket/port racket/file "../probe.rkt")

(define sorried-program
  (string-append
    "#lang the-little-prover\n" ; line 1
    "defun pair(x, y):\n" ; line 2
    "  cons(x, cons(y, '[]'))\n" ; line 3
    "dethm first_of_pair(a, b):\n" ; line 4
    "  equal(car(pair(a, b)), a)\n" ; line 5
    "proof:\n" ; line 6
    "  pair(a, b)\n" ; line 7
    "  sorry\n")) ; line 8

(define f (make-temporary-file "tlp-probe-~a.rkt"))
(display-to-file sorried-program f #:exists 'replace)

(define (probe-claim line)
  (define out (with-output-to-string (lambda () (probe-cli (path->string f) line))))
  (hash-ref (string->jsexpr out) 'claim))

;; cursor on the sorry: the claim it reports
(check-equal? (probe-claim 8) "equal(car(cons(a, cons(b, '[]'))), a)")
;; cursor on the completed step: the claim after it
(check-equal? (probe-claim 7) "equal(car(cons(a, cons(b, '[]'))), a)")

(delete-file f)
