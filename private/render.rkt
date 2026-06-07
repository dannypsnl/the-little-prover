#lang racket/base
;; Render book terms in surface notation for error messages.
(require racket/match racket/string "surface.rkt")

(provide term->surface)

(define (term->surface e)
  (match e
    [(list 'quote d) (format "'~a'" (datum->surface d))]
    [(list 'if q a el)
     (format "if(~a, ~a, ~a)"
             (term->surface q) (term->surface a) (term->surface el))]
    [(cons f args)
     (format "~a(~a)" (book->surface f)
             (string-join (map term->surface args) ", "))]
    [(? symbol? x) (symbol->string x)]
    [_ (format "~s" e)]))

(define (datum->surface d)
  (match d
    [(? list?) (format "[~a]" (string-join (map datum->surface d) ", "))]
    [_ (format "~a" d)]))
