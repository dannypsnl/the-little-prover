#lang racket/base
;; Diagnostic proof checker. J-Bob's own rewriting silently skips a step
;; that doesn't apply; here we re-drive each proof one rewrite/step at a
;; time so failures carry a reason, the current claim, and a syntax object
;; (for #lang error locations).
(require racket/match racket/list "core.rkt")

(provide (struct-out entry) (struct-out check-failure) check-program)

;; def/seed/steps are book S-expressions; def-stx and step-stxs (parallel
;; to steps) are syntax objects or #f, used only for error locations.
(struct entry (def seed steps def-stx step-stxs) #:transparent)

(struct check-failure (message stx claim) #:transparent)

(define (true? v) (eq? v 't))
(define (oops msg stx claim) (raise (check-failure msg stx claim)))

;; ---------- step addressing ----------
;; A step is either book-shaped, (path app), meaning "exactly here", or
;; (within prefix app), meaning "the unique place under prefix where the
;; rule applies". Resolution never touches the kernel's logic: we just
;; try the kernel's rewrite/step at every candidate path and keep the
;; ones that change the claim.

(define (step-parts s)
  (match s
    [(list 'within prefix app) (values 'within prefix app)]
    [(list path app) (values 'exact path app)]))

;; subterm of e at path, or #f
(define (focus-at e path)
  (match* (e path)
    [(_ '()) e]
    [((list 'if q a el) (cons d rest))
     (case d
       [(Q) (focus-at q rest)]
       [(A) (focus-at a rest)]
       [(E) (focus-at el rest)]
       [else #f])]
    [((list 'quote _) _) #f]
    [((cons _ args) (cons (? exact-positive-integer? d) rest))
     (and (<= d (length args)) (focus-at (list-ref args (sub1 d)) rest))]
    [(_ _) #f]))

;; all paths into e, preorder
(define (term-paths e)
  (cons '()
        (match e
          [(list 'quote _) '()]
          [(list 'if q a el)
           (append (map (lambda (p) (cons 'Q p)) (term-paths q))
                   (map (lambda (p) (cons 'A p)) (term-paths a))
                   (map (lambda (p) (cons 'E p)) (term-paths el)))]
          [(cons _ args)
           (for*/list ([(a i) (in-indexed (in-list args))]
                       [p (in-list (term-paths a))])
             (cons (add1 i) p))]
          [_ '()])))

(define (paths-under e prefix)
  (define sub (focus-at e prefix))
  (if sub
      (for/list ([p (in-list (term-paths sub))]) (append prefix p))
      '()))

;; The lhs instances of a rule application, for preferring "forward"
;; rewrites (unfold a defun, use a theorem's equality left-to-right)
;; when a search is otherwise ambiguous.
(define (rule-lhss defs app)
  (define name (car app))
  (define args (cdr app))
  (define def (findf (lambda (d) (and (pair? d) (pair? (cdr d))
                                      (eq? (cadr d) name)))
                     defs))
  (cond
    ;; not in defs: a built-in evaluation step like (atom '()); forward
    ;; means evaluating the application itself
    [(not def) (list (cons name args))]
    [(eq? (car def) 'defun) (list (cons name args))]
    [(eq? (car def) 'dethm)
     (define sub (map cons (caddr def) args))
     (define (subst e)
       (match e
         [(list 'quote _) e]
         [(? symbol? x) (cond [(assq x sub) => cdr] [else x])]
         [(cons f es) (cons f (map subst es))]
         [_ e]))
     (let lhss ([e (subst (cadddr def))])
       (match e
         [(list 'equal l _) (list l)]
         [(list 'if _ a el) (append (lhss a) (lhss el))]
         [_ '()]))]
    [else '()]))

(define (path->surface path)
  (format "[~a]" (apply string-append
                        (add-between (map (lambda (d) (format "~a" d)) path)
                                     ", "))))

;; → (values resolved-book-step new-claim)
(define (resolve-step defs claim s stx)
  (define-values (mode prefix app) (step-parts s))
  (case mode
    [(exact)
     (define next (rewrite/step defs claim (list prefix app)))
     (when (equal? next claim)
       (oops "step does not apply (focus does not match the rule instance here)"
             stx claim))
     (values (list prefix app) next)]
    [(within)
     (define candidates
       (for*/list ([p (in-list (paths-under claim prefix))]
                   [next (in-value (rewrite/step defs claim (list p app)))]
                   #:unless (equal? next claim))
         (cons p next)))
     (define picked
       (cond
         [(null? candidates) '()]
         [(null? (cdr candidates)) candidates]
         [else ; prefer the forward direction: focus = an lhs instance
          (define lhss (rule-lhss defs app))
          (define forward
            (for/list ([c (in-list candidates)]
                       #:when (member (focus-at claim (car c)) lhss))
              c))
          (if (and (pair? forward) (null? (cdr forward))) forward candidates)]))
     (cond
       [(null? picked)
        (oops (format "rule does not apply anywhere within ~a"
                      (path->surface prefix))
              stx claim)]
       [(pair? (cdr picked))
        (oops (format "ambiguous: rule applies at ~a; pick one with at/within"
                      (apply string-append
                             (add-between (map (lambda (c) (path->surface (car c)))
                                               picked)
                                          " and ")))
              stx claim)]
       [else (values (list (caar picked) app) (cdar picked))])]))

;; check-program : defs (listof entry) -> (values defs (listof (list stx before after)))
;; Returns the extended defs and a flat list of per-step states in proof order.
(define (check-program defs entries)
  (let loop ([defs defs] [entries entries] [acc '()])
    (if (null? entries)
        (values defs acc)
        (let-values ([(new-defs states) (check-entry defs (car entries))])
          (loop new-defs (cdr entries) (append acc states))))))

(define (check-entry defs ent)
  (match-define (entry def seed steps def-stx step-stxs) ent)
  ;; `sorry` reports the claim at that point; steps after it are not
  ;; checked (unlike Lean's, it does not admit — nothing gets past the
  ;; kernel)
  (define sorry-idx (index-of steps 'sorry))
  (define live-steps (if sorry-idx (take steps sorry-idx) steps))
  (define live-stxs (if sorry-idx (take step-stxs sorry-idx) step-stxs))
  (define check-steps
    (for/list ([s (in-list live-steps)])
      (define-values (mode prefix app) (step-parts s))
      (list prefix app)))
  (define pf (cons def (cons seed check-steps)))
  ;; 1. well-formedness
  (unless (true? (proofs? defs (list pf)))
    (cond
      [(not (true? (defs? defs (list def))))
       (oops "ill-formed definition (unbound variable, bad arity, or duplicate name)"
             def-stx #f)]
      [(not (true? (proofs? defs (list (cons def (cons seed '()))))))
       (oops "invalid measure or induction seed" def-stx #f)]
      [else
       (for ([s (in-list check-steps)] [stx (in-list live-stxs)])
         (unless (true? (step? defs s))
           (oops "ill-formed step (unknown rule, wrong arity, or unbound variable)"
                 stx #f)))
       (oops "ill-formed proof" def-stx #f)]))
  ;; 2. drive the proof one step at a time, collecting before/after states
  (define claim0 (rewrite/prove defs def seed '()))
  (define-values (final resolved states)
    (for/fold ([claim claim0] [resolved '()] [states '()])
              ([s (in-list live-steps)] [stx (in-list live-stxs)])
      (define before claim)
      (define-values (rs next) (resolve-step defs claim s stx))
      (values next (cons rs resolved) (cons (list stx before next) states))))
  ;; a sorry reports where the proof stands, at its location
  (when sorry-idx
    (define sorry-stx (list-ref step-stxs sorry-idx))
    (oops (if (equal? final ''t)
              "sorry, but the claim is already 't; delete this step"
              "sorry: the proof is unfinished (fill in the next step)")
          sorry-stx final))
  ;; 3. claim must reach 't
  (unless (equal? final ''t)
    (oops "proof ends but the claim is not yet 't" def-stx final))
  ;; 4. hand to J-Bob kernel
  (define new-defs
    (J-Bob/define defs (list (cons def (cons seed (reverse resolved))))))
  (unless (> (length new-defs) (length defs))
    (oops "definition rejected by J-Bob" def-stx final))
  (values new-defs (reverse states)))
