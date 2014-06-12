# Copyright 2014 The ALIVe authors.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import argparse, collections, sys, time
from z3 import *
from language import *
from parser import parse_llvm, parse_opt_file


def get_var_int_size(var, types):
  return types.evaluate(Int('t'+var)).as_long()


def mk_and(l):
  if len(l) == 0:
    return BoolVal(True)
  if len(l) == 1:
    return l[0]
  return And(l)


def block_model(s):
  m = s.model()
  s.add(Not(And([Int(str(n)) == m[n] for n in m.decls()])))


def str_model(s, v):
  val = s.model().evaluate(v, True).as_long()
  return "%d (%s)" % (val, hex(val))


def print_model(s):
  m = s.model()
  for d in m.decls():
    print '%s = %s' % (d, m[d])


def print_var_vals(s, vars, stopv, types):
  for k,v in vars.iteritems():
    if k == stopv:
      return
    if isinstance(v, Constant):
      continue
    defv = []
    bits = get_var_int_size(k, types)
    print "%s i%d = %s" % (k, bits, s.model().evaluate(v.toSMT(defv)))


def check_opt(src, tgt, types):
  s = Solver()
  for k,v in src.iteritems():
    if isinstance(v, Input) or isinstance(v, Constant):
      continue

    # skip instructions only on one side; assumes they remain unchanged
    if not tgt.has_key(k):
      continue

    defa = []
    defb = []
    a = v.toSMT(defa)
    b = tgt[k].toSMT(defb)
    defb = mk_and(defb)

    s.push()
    s.add(defa)

    # check if domain of defined values of Src implies that of Tgt
    s.push()
    s.add(Not(defb))
    if s.check() != unsat:
      print '\nDomain of definedness of Target is smaller than Source\'s for '+\
              'i%d %s' % (get_var_int_size(k, types), k)
      print 'Example:'
      print_var_vals(s, src, k, types)
      print 'Source val: ' + str_model(s, a)
      print 'Target val: undef'
      s.pop(2)
      exit(-1)
    s.pop()

    s.add(a != b)
    if s.check() != unsat:
      print '\nMismatch in values of i%d %s' % (get_var_int_size(k, types), k)
      print 'Example:'
      print_var_vals(s, src, k, types)
      print 'Source val: ' + str_model(s, a)
      print 'Target val: ' + str_model(s, b)
      s.pop()
      exit(-1)
    s.pop()


def main():
  file = sys.stdin.read()
  data = parse_opt_file(file)

  src = collections.OrderedDict()
  parse_llvm(data[0], src)

  tgt = collections.OrderedDict()
  parse_llvm(data[1], tgt)

  print 'Source:'
  print_prog(src)

  print '\nTarget:'
  print_prog(tgt)
  print

  # infer allowed types for registers
  type_vars = []
  type_src = getTypeConstraints(src, type_vars)
  type_tgt = getTypeConstraints(tgt, type_vars)

  s = Solver()
  s.add(type_src)
  s.add([v > 0 for v in type_vars])

  if s.check() != sat:
    print 'Source program does not type check'
    exit(-1)

  s.add(type_tgt)
  if s.check() != sat:
    print 'Source and Target programs do not type check'
    exit(-1)

  s.add([v <= 64 for v in type_vars])
  if s.check() != sat:
    print 'Currently limited to 64-bits registers'
    exit(-1)


  # now check for equivalence
  proofs = 0
  while s.check() == sat:
    proofs += 1
    sys.stdout.write('\rDone: ' + str(proofs))
    sys.stdout.flush()
    fixupTypes(src, s.model())
    fixupTypes(tgt, s.model())
    check_opt(src, tgt, s.model())
    block_model(s)

  print '\nOptimization is correct!'
  if s.check() != unsat:
    print 'Note: verification incomplete; did not check all bit widths'


if __name__ == "__main__":
  try:
    main()
  except KeyboardInterrupt:
    print '\nCaught Ctrl-C. Exiting..'
