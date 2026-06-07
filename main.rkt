#lang racket/base
;; The #lang the-little-prover language module. The reader hands us the
;; whole shrubbery parse; we lower it, check every proof against the
;; book's prelude at expansion time, and leave behind the checked
;; definitions plus a report printer.
(require (for-syntax racket/base
                     "private/core.rkt"
                     "private/check.rkt"
                     "private/surface.rkt"
                     "private/render.rkt"))

(provide (rename-out [tlp-module-begin #%module-begin])
         #%datum #%top #%app #%top-interaction)

(define-syntax (tlp-module-begin stx)
  (syntax-case stx ()
    [(_ body)
     (let ()
       (define entries (parse-program #'body))
       (define-values (final-defs _step-states)
         (with-handlers
           ([check-failure?
             (lambda (f)
               (raise-syntax-error
                 'the-little-prover
                 (if (check-failure-claim f)
                     (format "~a\n  current claim: ~a"
                             (check-failure-message f)
                             (term->surface (check-failure-claim f)))
                     (check-failure-message f))
                 (check-failure-stx f)))])
           (check-program (prelude) entries)))
       (define names
         (for/list ([e (in-list entries)]) (cadr (entry-def e))))
       (with-syntax ([defs-d final-defs] [names-d names])
         #'(#%module-begin
             (define defs 'defs-d)
             (define proved-names 'names-d)
             (provide defs proved-names)
             (module+ main
               (for-each (lambda (n) (printf "✓ ~a\n" n)) proved-names)
               (printf "QED\n")))))]))
