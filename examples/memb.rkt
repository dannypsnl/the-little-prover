#lang the-little-prover

defun memb(xs):
  measure: size(xs)
  if atom(xs):
    'nil'
  else if equal(car(xs), '?'):
    't'
  else:
    memb(cdr(xs))
proof:
  natp_size(xs)
  if_true(if(atom(xs), 't', if(equal(car(xs), '?'), 't', size(cdr(xs)) < size(xs))), 'nil')
  size_cdr(xs)
  if_same(equal(car(xs), '?'), 't')
  if_same(atom(xs), 't')

defun remb(xs):
  measure: size(xs)
  if atom(xs):
    '[]'
  else if equal(car(xs), '?'):
    remb(cdr(xs))
  else:
    cons(car(xs), remb(cdr(xs)))
proof:
  natp_size(xs)
  if_true(if(atom(xs), 't', size(cdr(xs)) < size(xs)), 'nil')
  size_cdr(xs)
  if_same(atom(xs), 't')

dethm memb_remb(xs):
  equal(memb(remb(xs)), 'nil')
proof induction(list_induction(xs)):
  within [A]: remb(xs)
  if_nest_A(atom(xs), '[]', if(equal(car(xs), '?'), remb(cdr(xs)), cons(car(xs), remb(cdr(xs)))))
  memb('[]')
  atom('[]')
  if_true('nil', if(equal(car('[]'), '?'), 't', memb(cdr('[]'))))
  equal_same('nil')
  remb(xs)
  if_nest_E(atom(xs), '[]', if(equal(car(xs), '?'), remb(cdr(xs)), cons(car(xs), remb(cdr(xs)))))
  if_same(equal(car(xs), '?'), memb(if(equal(car(xs), '?'), remb(cdr(xs)), cons(car(xs), remb(cdr(xs))))))
  if_nest_A(equal(car(xs), '?'), remb(cdr(xs)), cons(car(xs), remb(cdr(xs))))
  if_nest_E(equal(car(xs), '?'), remb(cdr(xs)), cons(car(xs), remb(cdr(xs))))
  equal_if(memb(remb(cdr(xs))), 'nil')
  memb(cons(car(xs), remb(cdr(xs))))
  atom_cons(car(xs), remb(cdr(xs)))
  if_false('nil', if(equal(car(cons(car(xs), remb(cdr(xs)))), '?'), 't', memb(cdr(cons(car(xs), remb(cdr(xs)))))))
  car_cons(car(xs), remb(cdr(xs)))
  cdr_cons(car(xs), remb(cdr(xs)))
  if_nest_E(equal(car(xs), '?'), 't', memb(remb(cdr(xs))))
  equal_if(memb(remb(cdr(xs))), 'nil')
  if_same(equal(car(xs), '?'), 'nil')
  equal_same('nil')
  if_same(equal(memb(remb(cdr(xs))), 'nil'), 't')
  if_same(atom(xs), 't')
