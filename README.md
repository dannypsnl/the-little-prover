# the-little-prover

*The Little Prover*'s J-Bob, with a shrubbery surface syntax.

## Installation

```sh
git clone https://github.com/dannypsnl/the-little-prover.git
cd the-little-prover
raco pkg install --auto
```

## Usage

```racket
#lang the-little-prover

defun pair(x, y):
  cons(x, cons(y, '[]'))

dethm first_of_pair(a, b):
  equal(car(pair(a, b)), a)
proof:
  pair(a, b)
  car_cons(a, cons(b, '[]'))
  equal_same(a)
```

To build a proof, start with `sorry` as the only step and run: the
checker stops there and prints the current claim. Insert the next
step before the `sorry`, run again, and delete it once the claim
reaches `'t'`. (Unlike Lean's `sorry`, it does not admit the claim —
the module errors until the proof is complete.)

Running a module checks every proof (a wrong step is a syntax error at
that step, with the current claim printed) and prints one ✓ per
definition:

```sh
$ racket examples/memb.rkt
✓ memb
✓ remb
✓ memb_remb
QED
```

See `examples/` for more: `basics.rkt` (the book's pair theorems),
`arith.rkt` (infix sugar, conditional claims), `memb.rkt` (recursive
defuns with `measure:` totality proofs and a `proof induction(…)`).
