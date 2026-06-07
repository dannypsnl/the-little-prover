#lang racket/base
(require rackunit
         (prefix-in j: "../private/j-bob-lang.rkt"))

;; total car/cdr: '() on atoms
(check-equal? (j:car '(a b)) 'a)
(check-equal? (j:car 'x) '())
(check-equal? (j:cdr '(a b)) '(b))
(check-equal? (j:cdr 42) '())
;; atom / equal return 't / 'nil
(check-equal? (j:atom '()) 't)
(check-equal? (j:atom (cons 1 2)) 'nil)
(check-equal? (j:equal 'a 'a) 't)
(check-equal? (j:equal 'a 'b) 'nil)
;; natp
(check-equal? (j:natp 0) 't)
(check-equal? (j:natp -1) 'nil)
(check-equal? (j:natp 'a) 'nil)
;; + and < treat non-numbers as 0
(check-equal? (j:+ 1 2) 3)
(check-equal? (j:+ 'a 2) 2)
(check-equal? (j:< 1 2) 't)
(check-equal? (j:< 2 1) 'nil)
;; if: anything non-'nil is true; branches are lazy
(check-equal? (j:if 't 1 (error "must not run")) 1)
(check-equal? (j:if 'nil (error "must not run") 2) 2)
(check-equal? (j:if 0 1 2) 1) ; 0 is true!
;; size
(check-equal? (j:size 'a) 0)
(check-equal? (j:size '(a b)) 2)
(check-equal? (j:size '((a) b)) 3)
