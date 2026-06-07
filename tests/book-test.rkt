#lang s-exp the-little-prover/private/j-bob-lang
;; Replay the whole book (vendor/little-prover.scm) as the port's oracle.
(require racket/include rackunit)

(include (file "../vendor/j-bob.scm"))
(include (file "../vendor/little-prover.scm"))

;; spot checks, expected values per the book
(check-equal? (chapter1.example1) ''ham)
(check-equal? (chapter1.example4) ''nil)
(check-equal? (chapter1.example9) '(equal (cons 'bagels '(and lox)) (cons x y)))

;; the full chain: every chapter's J-Bob/define succeeded iff the last
;; definition in the final context is align/align (a failed J-Bob/define
;; returns its input defs unchanged, so any failure anywhere breaks this).
(define final-defs (dethm.align/align))
(check-equal? (car (cdr (car (reverse final-defs)))) 'align/align)
