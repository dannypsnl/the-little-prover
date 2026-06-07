#lang scribble/manual
@require[scribble/core
         @for-label[the-little-prover/j-bob
                    racket/base]]

@(define (surface . strs)
   (nested #:style 'code-inset (apply verbatim strs)))

@; inline code, like @tt but without smart-quote decoding, so 't and
@; '[] keep their straight quotes.
@(define (c . content)
   (elem #:style 'tt (for/list ([x (in-list content)])
                       (if (string? x) (literal x) x))))

@; the focus: the subterm a proof step rewrites, highlighted in the
@; claim. background-color-property renders in both HTML and LaTeX.
@(define focus-style
   (style 'tt (list (background-color-property (list #xFF #xE3 #x8C)))))
@(define (focus . strs)
   (elem #:style focus-style (apply literal strs)))

@title{the-little-prover}
@author{dannypsnl}

@emph{The Little Prover}'s J-Bob prover (Friedman & Eastlund), ported to
Racket and wrapped in a shrubbery surface syntax.
@c{#lang the-little-prover} is a proof-script language: a module is a
sequence of @c{defun} and @c{dethm} definitions, each with a
@c{proof:} block of rewriting steps, checked at expansion time against
the book's axioms. A step that does not apply is a syntax error at that
step, with the current claim printed. Running a module prints one ✓ per
checked definition.

The book's S-expression API is also available
(@secref["j-bob-api"]); the reference implementation is vendored under
@c{vendor/} and runs unmodified as the kernel, so it has the final word
on every proof.

@table-of-contents[]

@section[#:tag "tour"]{A guided tour}

A theorem's claim is a goal to be rewritten: it starts as the
theorem's body, each proof step rewrites one subterm of it, and the
proof is complete when the claim reaches @c{'t'}. This tour proves
one theorem and shows, for every step, the claim before, the subterm
the step rewrites, and the claim after.

@surface|{
#lang the-little-prover

defun pair(x, y):
  cons(x, cons(y, '[]'))

dethm first_of_pair(a, b):
  equal(car(pair(a, b)), a)
proof:
  pair(a, b)
  car_cons(a, cons(b, '[]'))
  equal_same(a)
}|

@c{pair} is a non-recursive total function, so it needs no proof.
@c{first_of_pair} claims that @c{car} of a pair is its first
element, and its proof is three steps. Each step names a @emph{rule
instance} — an axiom, an earlier theorem, or a definition, applied to
specific arguments — read as an equation whose one side matches a
subterm of the claim.

@bold{Step 1 — @c{pair(a, b)}: unfold a definition.} The claim
mentions @c{pair}, and a @c{defun} in scope is a rule equating its
application with its body: @c{pair(x, y) = cons(x, cons(y, '[]'))}.
The step is that rule at @c{x = a}, @c{y = b}. Its left-hand side
@c{pair(a, b)} matches the highlighted subterm — the @emph{focus} —
which the step replaces with the right-hand side:

@verbatim|{
claim:  equal(car(|@focus{pair(a, b)}), a)
step:   pair(a, b)                       by  pair(x, y) = cons(x, cons(y, '[]'))

claim:  equal(car(cons(a, cons(b, '[]'))), a)
}|

@bold{Step 2 — @c{car_cons(a, cons(b, '[]'))}: apply an axiom.} The
new claim contains @c{car(cons(@racketvarfont{...}))}, the shape of
the axiom @c{car_cons(x, y)}, which says @c{car(cons(x, y)) = x}.
The step names the instance with the arguments exactly as they stand
in the claim, @c{x = a} and @c{y = cons(b, '[]')}; the focus
collapses to @c{a}:

@verbatim|{
claim:  equal(|@focus{car(cons(a, cons(b, '[]')))}, a)
step:   car_cons(a, cons(b, '[]'))       by  car(cons(x, y)) = x

claim:  equal(a, a)
}|

@bold{Step 3 — @c{equal_same(a)}: finish.} @c{equal(a, a)} is the
left-hand side of the axiom @c{equal_same(x)} at @c{x = a}, whose
right-hand side is @c{'t'}:

@verbatim|{
claim:  |@focus{equal(a, a)}
step:   equal_same(a)                    by  equal(x, x) = 't'

claim:  't'
}|

The claim is @c{'t'}, so the proof is complete; running the module
prints

@verbatim|{
✓ pair
✓ first_of_pair
QED
}|

The instance must be exact. Writing the sloppy @c{car_cons(a, b)} as
step 2 is an error — @c{ambiguous: rule applies at [1, 1, 1] and
[2]; pick one with at/within} — because its left-hand side
@c{car(cons(a, b))} appears nowhere in the claim, and since equations
also rewrite right to left, the step could only turn an @c{a}
@emph{backwards} into @c{car(cons(a, b))}, at either of two places.
The checker refuses to guess.

@bold{Finding the steps.} You never have to track the claim by hand:
a proof may contain the step @c{sorry}, and the checker stops there
and reports — as a syntax error at that line — the claim it was
facing. So every proof starts as

@surface|{
proof:
  sorry
}|

and running the module prints

@verbatim|{
tour.rkt:9:2: the-little-prover: sorry: the proof is unfinished (fill in the next step)
  current claim: equal(car(pair(a, b)), a)
}|

The loop: read the claim, find the rule whose side matches, insert it
@emph{before} the @c{sorry}, run again. After inserting @c{pair(a, b)}
the @c{sorry} reports
@c{current claim: equal(car(cons(a, cons(b, '[]'))), a)} — the trace
above, one run at a time. When the claim reaches @c{'t'}, the
@c{sorry} says so; delete it and the proof is done. (Steps after a
@c{sorry} are not checked.)

@c{sorry} matters most when you cannot predict the claim at all:
@c{proof induction(@racketvarfont{seed}):} and the totality proofs of
recursive @c{defun}s start from a claim the checker generates (see
@secref["proofs"]) — put a @c{sorry} in and the checker shows it to
you. The VSCode extension under @c{vscode-extension/} shows the claim
at the cursor in a panel (@c{ctrl+alt+p}), saving the run loop.

@section{The language}

@defmodulelang[the-little-prover]

A module is a sequence of definitions, each followed by its proof:

@surface|{
defun name(var, ...):
  measure: term          // optional; required iff the defun is recursive
  body

dethm name(var, ...):
  claim

proof:                   // or: proof induction(seed):
  step
  ...
}|

Definitions are checked in order at expansion time, each extending the
context, so later proofs may use earlier @c{defun}s and @c{dethm}s as
rules. The initial context is the book's @racket[prelude]: the axioms
plus @c{list_induction} and @c{star_induction}.

A checked module provides two bindings: @racketidfont{defs}, the final context
as book S-expressions, and @racketidfont{proved-names}, the list of names
proved in the module. Run as a main program, the module prints
@c{✓ @racketvarfont{name}} for each and @c{QED}.

@subsection{Terms}

@itemlist[

@item{@bold{Variables} — identifiers: @c{x}, @c{xs}.}

@item{@bold{Naturals} — literals @c{0}, @c{1}, @c{2}, …, shorthand
for the corresponding quoted constants.}

@item{@bold{Quoted data} — @c{'@racketvarfont{datum}'} where the datum is a
symbol, an integer, an operator name, or a bracketed list:
@c{'t'}, @c{'nil'}, @c{'[]'}, @c{'ham'}, @c{'?'},
@c{'[eggs, toast]'}. @c{'t'} and @c{'nil'} are the booleans.}

@item{@bold{Applications} — @c{f(t, ...)}, where @c{f} is a built-in
or any @c{defun} in scope. The built-ins are @c{cons}, @c{car},
@c{cdr}, @c{atom}, @c{equal}, @c{natp}, @c{size}, @c{+},
@c{<}. All are total: @c{car} and @c{cdr} of an atom are @c{'[]'},
@c{+} and @c{<} treat non-numbers as @c{0}, and @c{if} treats any
non-@c{'nil'} value as true.}

@item{@bold{Infix sugar} — @c{t == u} for @c{equal(t, u)}, and
@c{t + u}, @c{t < u}. One infix operator per group; parenthesize to
nest: @c{(a + b) == (b + a)}.}

@item{@bold{Conditionals} — @c{if @racketvarfont{c}: @racketvarfont{t}} chains with
@c{else if} and a mandatory final @c{else:} (all functions are
total). Conditions and branches are terms; branches may be nested
chains.}

]

@subsection{Definitions}

@c{defun} defines a function. A non-recursive @c{defun} needs no
measure and no proof. A recursive @c{defun} must declare
@c{measure: @racketvarfont{term}} as the first line of its body and supply a
totality proof: the claim — built by the checker — is that the measure
is a natural and strictly decreases at every recursive call.

@c{dethm} states a theorem. Its claim is a term, typically an @c{==}
equation or a conditional chain whose tests are the premises; it always
needs a proof.

@subsection[#:tag "proofs"]{Proofs}

A proof is introduced by @c{proof:} or
@c{proof induction(@racketvarfont{seed}):}. The seed is an application of a
recursive @c{defun} in scope to the claim's variables — e.g.
@c{list_induction(xs)} — and turns the claim into the book's
induction claim for that function's recursion structure: one case per
branch, with the inductive hypotheses as premises. A @c{defun} takes
@c{measure:}, never @c{induction}.

Each step is a rule instance in one of three forms — or a @c{sorry}:

@itemlist[

@item{@c{rule(args)} — the checker searches the whole claim for places
where the instance applies. If there is exactly one, it is used. If
there are several, the checker prefers the @emph{forward} one — the
place whose focus is the rule's left-hand side instance (unfolding a
@c{defun}, using an equation left to right) — and uses it when it is
unique; otherwise the step is an error listing the candidate paths.}

@item{@c{within [prefix]: rule(args)} — the same search, restricted to
the subterm at @c{prefix}.}

@item{@c{at [path]: rule(args)} — the book's exact addressing; the
rule must apply at precisely that focus.}

@item{@c{sorry} — the checker stops here and reports the current
claim as a syntax error at this line. Steps after the @c{sorry} are
not checked. Use it to build a proof incrementally (see
@secref["tour"]) — every @c{proof:} can start as a lone @c{sorry}.
Unlike Lean's @c{sorry}, it does not admit the claim: nothing gets
past the kernel, so the module does not compile until the @c{sorry}
is gone.}

]

Path elements are argument positions @c{1}, @c{2}, … and @c{Q},
@c{A}, @c{E} for the question, answer, and else of an @c{if}.

A rule whose claim is conditional rewrites only where its premises hold:
inside the answer branch of an @c{if} on that premise (or the else
branch, for a refuted premise). Premises introduced by
@c{proof induction} are used the same way. From
@c{examples/arith.rkt}:

@surface|{
dethm zero_plus(n):
  if natp(n):
    (0 + n) == n
  else:
    't'
proof:
  identity_plus(n)
  equal_same(n)
  if_same(natp(n), 't')
}|

@c{identity_plus(n)} only applies under the premise @c{natp(n)}, so
the checker rewrites in the answer branch, where the premise holds.

The final step must bring the claim to @c{'t'}.

@subsection{Errors}

Every failure is a syntax error located at the offending step (or
definition), with the current claim attached. The messages:

@itemlist[

@item{@c{step does not apply} — an @c{at} step whose focus does not
match the rule instance.}

@item{@c{rule does not apply anywhere within [...]} — a bare or
@c{within} step that matched nothing.}

@item{@c{ambiguous: rule applies at [...] and [...]; pick one with at/within} — a bare or
@c{within} step that matched several places; pick one with @c{at} or
narrow the @c{within} prefix.}

@item{@c{proof ends but the claim is not yet 't} — more steps
needed.}

@item{@c{sorry: the proof is unfinished (fill in the next step)} — a
@c{sorry} step; the claim printed is where the proof stands. When the
proof is already complete, it instead says @c{sorry, but the claim is
already 't; delete this step}.}

@item{@c{a defun with a measure needs a totality proof}, @c{a dethm
needs a proof}, @c{if without a final else}, and ill-formedness errors
(unbound variable, wrong arity, duplicate name, unknown rule) — raised
while parsing or well-formedness checking.}

]

@section{Rules}

Every step names a rule instance: one of the book's axioms (their
surface names replace @c{/}, @c{-}, and @c{+} with @c{_} or words),
a @c{defun} or @c{dethm} already in scope, or built-in evaluation.
Equations are oriented left to right for the bare-step search's forward
preference, but @c{at}/@c{within} steps may rewrite in either
direction. ``Under premise @racketvarfont{p}'' marks a conditional rule: it
rewrites only where @racketvarfont{p} is known to hold.

@subsection{cons}

@itemlist[

@item{@c{atom_cons(x, y)} — @c{atom(cons(x, y)) = 'nil'}. Book:
@c{atom/cons}.}

@item{@c{car_cons(x, y)} — @c{car(cons(x, y)) = x}. Book:
@c{car/cons}.}

@item{@c{cdr_cons(x, y)} — @c{cdr(cons(x, y)) = y}. Book:
@c{cdr/cons}.}

@item{@c{cons_car_cdr(x)} — @c{cons(car(x), cdr(x)) = x}, under
premise @c{atom(x) = 'nil'}. Book: @c{cons/car+cdr}.}

]

@subsection{equal}

@itemlist[

@item{@c{equal_same(x)} — @c{equal(x, x) = 't'}. Book:
@c{equal-same}.}

@item{@c{equal_swap(x, y)} — @c{equal(x, y) = equal(y, x)}. Book:
@c{equal-swap}.}

@item{@c{equal_if(x, y)} — @c{equal(x, y) = 't'}, under premise
@c{equal(x, y)}. Book: @c{equal-if}.}

]

@subsection{if}

@itemlist[

@item{@c{if_true(x, y)} — @c{if('t', x, y) = x}. Book:
@c{if-true}.}

@item{@c{if_false(x, y)} — @c{if('nil', x, y) = y}. Book:
@c{if-false}.}

@item{@c{if_same(x, y)} — @c{if(x, y, y) = y}. Book: @c{if-same}.}

@item{@c{if_nest_A(x, y, z)} — @c{if(x, y, z) = y}, under premise
@c{x}. Book: @c{if-nest-A}.}

@item{@c{if_nest_E(x, y, z)} — @c{if(x, y, z) = z}, under the
refuted premise @c{x} (where @c{x} is known @c{'nil'}). Book:
@c{if-nest-E}.}

]

@subsection{size}

@itemlist[

@item{@c{natp_size(x)} — @c{natp(size(x)) = 't'}. Book:
@c{natp/size}.}

@item{@c{size_car(x)} — @c{(size(car(x)) < size(x)) = 't'}, under
premise @c{atom(x) = 'nil'}. Book: @c{size/car}.}

@item{@c{size_cdr(x)} — @c{(size(cdr(x)) < size(x)) = 't'}, under
premise @c{atom(x) = 'nil'}. Book: @c{size/cdr}.}

]

@subsection{Arithmetic}

@itemlist[

@item{@c{associate_plus(a, b, c)} — @c{((a + b) + c) = (a + (b +
c))}. Book: @c{associate-+}.}

@item{@c{commute_plus(x, y)} — @c{(x + y) = (y + x)}. Book:
@c{commute-+}.}

@item{@c{identity_plus(x)} — @c{(0 + x) = x}, under premise
@c{natp(x)}. Book: @c{identity-+}.}

@item{@c{natp_plus(x, y)} — @c{natp(x + y) = 't'}, under premises
@c{natp(x)} and @c{natp(y)}. Book: @c{natp/+}.}

@item{@c{positives_plus(x, y)} — @c{(0 < (x + y)) = 't'}, under
premises @c{0 < x} and @c{0 < y}. Book: @c{positives-+}.}

@item{@c{common_addends_lt(x, y, z)} — @c{((x + z) < (y + z)) = (x <
y)}. Book: @c{common-addends-<}.}

]

@subsection{Induction seeds}

@c{list_induction(x)} and @c{star_induction(x)} (book:
@c{list-induction}, @c{star-induction}) are recursive @c{defun}s
provided by the prelude with their totality proofs already done.
@c{list_induction} recurses on @c{cdr} — induction over lists;
@c{star_induction} recurses on both @c{car} and @c{cdr} — induction
over trees. Use them as @c{proof induction(...)} seeds; like any
@c{defun} in scope, they can also be unfolded as steps.

@subsection{Definitions and theorems as rules}

A @c{defun} @c{f} in scope is a rule: the step @c{f(args)} rewrites
between the application and its body with @c{args} substituted for the
formals — forward means unfolding. A @c{dethm} in scope is likewise a
rule: its claim, instantiated at the step's arguments; equations rewrite
in either direction (forward is left to right), and conditional claims
apply only under their premises.

@subsection{Evaluation}

An application of a built-in to wholly quoted arguments is itself a
rule: the step rewrites the application to its value. For example, the
step @c{atom('[]')} rewrites @c{atom('[]')} to @c{'t'} in
@c{examples/memb.rkt}.

@section[#:tag "j-bob-api"]{The book's S-expression API}

@defmodule[the-little-prover/j-bob]

The reference implementation's entry points, running verbatim (the
vendored @c{j-bob.scm} is @racket[include]d under a port of the book's
host shim). Terms, definitions, proofs, and steps use exactly the book's
S-expression shapes.

@racketblock[
(require the-little-prover/j-bob)
(J-Bob/step (prelude) '(car (cons 'ham '(eggs)))
  '(((1) (cons 'ham '(eggs)))))
]

@defproc[(J-Bob/step [defs list?] [e list?] [steps list?]) list?]{
Applies @racket[steps] (each @racket[(path (rule arg ...))]) to the
expression @racket[e] under context @racket[defs]; a step that does not
apply leaves the expression unchanged.}

@defproc[(J-Bob/prove [defs list?] [pfs list?]) list?]{
Checks the proofs @racket[pfs]; returns the final claim, @racket['(quote t)]
when every proof is complete, or @racket['(quote nil)] if the proofs are
malformed.}

@defproc[(J-Bob/define [defs list?] [pfs list?]) list?]{
Extends @racket[defs] with each definition in @racket[pfs] whose proof
succeeds; on failure returns the context unchanged.}

@defproc[(axioms) list?]{The book's initial axioms.}

@defproc[(prelude) list?]{@racket[(axioms)] plus @c{list-induction} and
@c{star-induction} with their totality proofs.}
