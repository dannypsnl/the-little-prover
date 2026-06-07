#lang racket/base
;; Lower parsed shrubbery groups to the book's S-expression terms, defs,
;; and proofs. Pure syntax→datum translation; proof *checking* lives in
;; check.rkt. `who` arguments are syntax objects used for error locations.
(require racket/match racket/list "check.rkt")

(provide parse-program parse-group-term surface->book book->surface
         (struct-out entry))

(define surface-book-names
  '((atom_cons . atom/cons) (car_cons . car/cons) (cdr_cons . cdr/cons)
                            (equal_same . equal-same) (equal_swap . equal-swap) (equal_if . equal-if)
                            (if_true . if-true) (if_false . if-false) (if_same . if-same)
                            (if_nest_A . if-nest-A) (if_nest_E . if-nest-E)
                            (cons_car_cdr . cons/car+cdr)
                            (natp_size . natp/size) (size_car . size/car) (size_cdr . size/cdr)
                            (associate_plus . associate-+) (commute_plus . commute-+)
                            (identity_plus . identity-+) (natp_plus . natp/+)
                            (positives_plus . positives-+) (common_addends_lt . common-addends-<)
                            (list_induction . list-induction) (star_induction . star-induction)))

(define (surface->book n)
  (cond [(assq n surface-book-names) => cdr] [else n]))
(define (book->surface n)
  (cond [(findf (lambda (p) (eq? (cdr p) n)) surface-book-names) => car]
        [else n]))

(define (perr who msg . args)
  (raise-syntax-error 'the-little-prover (apply format msg args) who))

(define (parse-group-term g who)
  (match g
    [(cons 'group es) (parse-term-elems es who)]
    [_ (perr who "expected a term")]))

(define (parse-term-elems es who)
  (define-values (lhs rest) (parse-atomic es who))
  (match rest
    ['() lhs]
    [(cons (list 'op o) more)
     (define f (case o
                 [(==) 'equal] [(+) '+] [(<) '<]
                 [else (perr who "unsupported operator: ~a" o)]))
     (define-values (rhs rest2) (parse-atomic more who))
     (unless (null? rest2)
       (perr who "chained infix operators need parentheses"))
     (list f lhs rhs)]
    [_ (perr who "cannot parse term: ~s" es)]))

(define (parse-atomic es who)
  (match es
    [(cons (? exact-nonnegative-integer? n) rest)
     (values `(quote ,n) rest)]
    [(cons (list 'quotes (cons 'group ds)) rest)
     (match ds
       [(list d) (values `(quote ,(quoted->datum d who)) rest)]
       [_ (perr who "a quoted constant must be a single datum")])]
    [(list-rest (? symbol? f) (cons 'parens arg-gs) rest)
     (values (cons (surface->book f)
                   (for/list ([ag (in-list arg-gs)])
                     (parse-group-term ag who)))
             rest)]
    [(cons (list 'parens g) rest)
     (values (parse-group-term g who) rest)]
    [(cons (? symbol? x) rest) (values x rest)]
    [_ (perr who "cannot parse term: ~s" es)]))

(define (quoted->datum d who)
  (match d
    [(? symbol?) d]
    [(? exact-integer?) d]
    [(list 'op o) o]
    [(cons 'brackets gs)
     (for/list ([g (in-list gs)])
       (match g
         [(list 'group e) (quoted->datum e who)]
         [_ (perr who "bad quoted list element")]))]
    [_ (perr who "unsupported quoted datum: ~s" d)]))

(define (block-if-group? g)
  (match g
    [(list-rest 'group 'if (and rest (cons _ _)))
     (match (last rest) [(cons 'block _) #t] [_ #f])]
    [_ #f]))

(define (parse-body gs who)
  (cond
    [(and (pair? gs) (block-if-group? (car gs)))
     (parse-if-chain gs who)]
    [(and (= (length gs) 1) (not (block-if-group? (car gs))))
     (parse-group-term (car gs) who)]
    [else (perr who "expected a single term or an if/else chain")]))

(define (split-at-block es who)
  (define-values (cond-es blks)
    (splitf-at es (lambda (e) (not (and (pair? e) (eq? (car e) 'block))))))
  (match blks
    [(list (cons 'block bgs)) (values cond-es bgs)]
    [_ (perr who "malformed if: expected exactly one block")]))

(define (parse-if-chain gs who)
  (match gs
    [(cons (list-rest 'group 'if cond+block) more)
     (define-values (cond-es bgs) (split-at-block cond+block who))
     `(if ,(parse-term-elems cond-es who)
          ,(parse-body bgs who)
          ,(parse-else more who))]
    [_ (perr who "malformed if chain")]))

(define (parse-else gs who)
  (match gs
    [(list (list 'group 'else (cons 'block bgs)))
     (parse-body bgs who)]
    [(cons (list-rest 'group 'else 'if rest) more)
     (parse-if-chain (cons (list* 'group 'if rest) more) who)]
    [_ (perr who "if without a final else (all functions are total)")]))

(define (parse-formals parens-d who)
  (for/list ([fg (in-list (cdr parens-d))])
    (match fg
      [(list 'group (? symbol? x)) x]
      [_ (perr who "formals must be plain identifiers")])))

(define (parse-defun d who)
  (match d
    [(list 'group 'defun (? symbol? name)
           (and formals (cons 'parens _)) (cons 'block bgs))
     (define-values (meas body-gs)
       (match bgs
         [(cons (list 'group 'measure (list 'block mg)) rest)
          (values (parse-group-term mg who) rest)]
         [_ (values #f bgs)]))
     (values `(defun ,name ,(parse-formals formals who)
                     ,(parse-body body-gs who))
             meas)]
    [_ (perr who "malformed defun: expected defun name(formals): body")]))

(define (parse-dethm d who)
  (match d
    [(list 'group 'dethm (? symbol? name)
           (and formals (cons 'parens _)) (cons 'block bgs))
     `(dethm ,name ,(parse-formals formals who) ,(parse-body bgs who))]
    [_ (perr who "malformed dethm: expected dethm name(formals): claim")]))

(define (stx-list stx) (or (syntax->list stx) (list stx)))

(define (locate stx)
  (define (find s)
    (cond
      [(not (syntax? s)) #f]
      [(syntax-line s) s]
      [else (ormap find (or (syntax->list s) '()))]))
  (define loc (find stx))
  (if loc (datum->syntax #f (syntax->datum stx) loc) stx))

(define (parse-path-elem g who)
  (match g
    [(list 'group (? exact-positive-integer? n)) n]
    [(list 'group (and s (or 'Q 'A 'E))) s]
    [_ (perr who "path elements are positive integers, Q, A, or E")]))

(define (parse-rule-app g who)
  (match g
    [(list 'group (? symbol? f) (cons 'parens arg-gs))
     (cons (surface->book f)
           (for/list ([ag (in-list arg-gs)]) (parse-group-term ag who)))]
    [_ (perr who "a step is rule(args)")]))

(define (parse-step step-stx)
  (match (syntax->datum step-stx)
    [(list 'group 'sorry) 'sorry]
    [(list 'group 'at (cons 'brackets path-gs) (list 'block rule-g))
     (list (for/list ([pg (in-list path-gs)]) (parse-path-elem pg step-stx))
           (parse-rule-app rule-g step-stx))]
    [(list 'group 'within (cons 'brackets path-gs) (list 'block rule-g))
     (list 'within
           (for/list ([pg (in-list path-gs)]) (parse-path-elem pg step-stx))
           (parse-rule-app rule-g step-stx))]
    [(and d (list 'group (? symbol?) (cons 'parens _)))
     (list 'within '() (parse-rule-app d step-stx))]
    [_ (perr step-stx
             "malformed step: expected `rule(args)`, `at [path]: rule(args)`, or `within [prefix]: rule(args)`")]))

(define (parse-proof proof-stx)
  (define parts (stx-list proof-stx))
  (define block-stx (last parts))
  (define head (map syntax->datum (drop-right (cdr parts) 1)))
  (define seed
    (match head
      ['(proof) #f]
      [(list 'proof 'induction (list 'parens g))
       (parse-group-term g proof-stx)]
      [_ (perr proof-stx
               "malformed proof: expected `proof:` or `proof induction(seed):`")]))
  (define step-stxs (cdr (stx-list block-stx))) ; drop the `block` head
  (values seed (map parse-step step-stxs) (map locate step-stxs)))

(define (proof-group? stx)
  (match (syntax->datum stx)
    [(list-rest 'group 'proof _) #t]
    [_ #f]))

(define (parse-program stx)
  (define groups (cdr (stx-list stx)))
  (let loop ([gs groups] [entries '()])
    (cond
      [(null? gs) (reverse entries)]
      [else
       (define g (locate (car gs)))
       (define d (syntax->datum g))
       (match d
         [(list-rest 'group 'defun _)
          (define-values (def meas) (parse-defun d g))
          (define-values (seed steps step-stxs rest)
            (attach-proof (cdr gs) g))
          (when (and meas (null? steps))
            (perr g "a defun with a measure needs a totality proof"))
          (when (and seed (not (eq? seed 'nil)))
            (perr g "a defun takes a measure: clause, not proof induction"))
          (loop rest
                (cons (entry def (if meas meas 'nil) steps g step-stxs)
                      entries))]
         [(list-rest 'group 'dethm _)
          (define def (parse-dethm d g))
          (define-values (seed steps step-stxs rest)
            (attach-proof (cdr gs) g))
          (when (and (null? steps) (eq? seed 'nil))
            (perr g "a dethm needs a proof"))
          (loop rest (cons (entry def seed steps g step-stxs) entries))]
         [(list-rest 'group 'proof _)
          (perr g "proof without a preceding defun or dethm")]
         [_ (perr g "expected defun, dethm, or proof")])])))

(define (attach-proof gs def-stx)
  (cond
    [(and (pair? gs) (proof-group? (car gs)))
     (define-values (seed steps step-stxs) (parse-proof (car gs)))
     (values (or seed 'nil) steps step-stxs (cdr gs))]
    [else (values 'nil '() '() gs)]))
