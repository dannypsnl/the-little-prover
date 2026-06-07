# Vendored reference implementation

`j-bob.scm`, `j-bob-lang.scm`, and `little-prover.scm` are the unmodified
reference implementation of J-Bob from *The Little Prover*
(Friedman & Eastlund), fetched from
https://github.com/the-little-prover/j-bob (scheme/ directory).
See LICENSE.md in this directory (BSD-2-Clause).

- `j-bob.scm` is `include`d verbatim by `private/core.rkt`.
- `little-prover.scm` (the book's chapters as runnable examples) is
  `include`d by `tests/book-test.rkt` as the test oracle.
- `j-bob-lang.scm` is kept for reference only; its Racket port is
  `private/j-bob-lang.rkt`.
