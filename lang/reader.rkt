#lang racket/base
;; #lang the-little-prover reader: shrubbery notation → a module whose
;; body is the parsed shrubbery tree; main.rkt's #%module-begin does the
;; lowering and proof checking at expansion time.
(require shrubbery/parse syntax/strip-context)

(provide read read-syntax get-info)

(define (read in) (syntax->datum (read-syntax #f in)))

(define (read-syntax src in)
  (port-count-lines! in)
  (define parsed (parse-all in #:source src))
  (strip-context
    #`(module prog the-little-prover/main
        #,parsed)))

(define (get-info in mod line col pos)
  (lambda (key default) default))
