#lang the-little-prover

// Infix sugar: `==` is equal, `+` is the book's total +.
dethm plus_swap(a, b):
  (a + b) == (b + a)
proof:
  commute_plus(a, b)
  equal_same(b + a)

// A conditional claim: identity_plus only applies under the premise
// natp(n) — the checker finds the spot where the premise holds.
dethm zero_plus(n):
  if natp(n):
    (0 + n) == n
  else:
    't'
proof:
  identity_plus(n)
  equal_same(n)
  if_same(natp(n), 't')
