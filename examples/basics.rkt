#lang the-little-prover

defun pair(x, y):
  cons(x, cons(y, '[]'))

defun second_of(x):
  car(cdr(x))

dethm first_of_pair(a, b):
  equal(car(pair(a, b)), a)
proof:
  pair(a, b)
  car_cons(a, cons(b, '[]'))
  equal_same(a)

dethm second_of_pair(a, b):
  equal(second_of(pair(a, b)), b)
proof:
  second_of(pair(a, b))
  pair(a, b)
  cdr_cons(a, cons(b, '[]'))
  car_cons(b, '[]')
  equal_same(b)
