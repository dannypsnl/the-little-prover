#lang s-exp "j-bob-lang.rkt"
;; J-Bob itself, included verbatim from the book's reference implementation.
(require racket/include)

(include (file "../vendor/j-bob.scm"))

(provide J-Bob/step J-Bob/prove J-Bob/define axioms prelude
         ;; internals re-used by the diagnostic checker (private/check.rkt)
         defs? proofs? steps? step? expr?
         rewrite/prove rewrite/step)
