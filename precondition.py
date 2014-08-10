# Copyright 2014 The ALIVe authors.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from language import *

class BoolPred:
  def fixupTypes(self, types):
    for attr in dir(self):
      a = getattr(self, attr)
      if isinstance(a, (Type, Value, BoolPred)):
        a.fixupTypes(types)
      if isinstance(a, tuple) and all(isinstance(v, (Type,Value,BoolPred)) for v in a):
        for v in a:
          v.fixupTypes(types)


################################
class TruePred(BoolPred):
  def __repr__(self):
    return 'true'

  def getTypeConstraints(self):
    return BoolVal(True)

  def toSMT(self, state):
    return BoolVal(True)


################################
class PredNot(BoolPred):
  def __init__(self, v):
    assert isinstance(v, BoolPred)
    self.v = v

  def __repr__(self):
    return '!%s' % self.v

  def getTypeConstraints(self):
    return self.v.getTypeConstraints()

  def toSMT(self, state):
    return Not(self.v.toSMT(state))


################################
class PredAnd(BoolPred):
  def __init__(self, *args):
    assert all(isinstance(v, BoolPred) for v in args)
    self.args = args

  def __repr__(self):
   return '(' + ' && '.join(repr(v) for v in self.args) + ')'

  def getTypeConstraints(self):
    return mk_and(v.getTypeConstraints() for v in self.args)

  def toSMT(self, state):
    return And([v.toSMT(state) for v in self.args])


################################
class PredOr(BoolPred):
  def __init__(self, *args):
    assert all(isinstance(v, BoolPred) for v in args)
    self.args = args

  def __repr__(self):
    return '(' + ' || '.join(repr(v) for v in self.args) + ')'

  def getTypeConstraints(self):
    return mk_and(v.getTypeConstraints() for v in self.args)

  def toSMT(self, state):
    return Or([v.toSMT(state) for v in self.args])


################################
class BinaryBoolPred(BoolPred):
  EQ, NE, SLT, SLE, SGT, SGE, Last = range(7)

  opnames = ['==', '!=', '<', '<=', '>', '>=']

  def __init__(self, op, v1, v2):
    assert 0 <= op < self.Last
    assert isinstance(v1, (Constant, Input))
    assert isinstance(v2, (Constant, Input))
    self.op = op
    self.v1 = v1
    self.v2 = v2

  def __repr__(self):
    return '(%s %s %s)' % (self.v1, self.opnames[self.op], self.v2)

  @staticmethod
  def getOpId(name):
    for i in range(BinaryBoolPred.Last):
      if BinaryBoolPred.opnames[i] == name:
        return i
    assert False

  def getTypeConstraints(self):
    return mk_and([self.v1.type == self.v2.type,
                   self.v1.getTypeConstraints(),
                   self.v2.getTypeConstraints()])

  def toSMT(self, state):
    v1 = self.v1.toSMT([], state, [])
    v2 = self.v2.toSMT([], state, [])
    return {
      self.EQ: lambda a,b: a == b,
      self.NE: lambda a,b: a != b,
      self.SLT: lambda a,b: a < b,
      self.SLE: lambda a,b: a <= b,
      self.SGT: lambda a,b: a > b,
      self.SGE: lambda a,b: a >= b,
    }[self.op](v1, v2)


################################
class LLVMBoolPred(BoolPred):
  isPower2, isSignBit, known, maskZero, NSWAdd, Last = range(6)

  opnames = {
    isPower2:  'isPowerOf2',
    isSignBit: 'isSignBit',
    known:     'Known',
    maskZero:  'MaskedValueIsZero',
    NSWAdd:    'WillNotOverflowSignedAdd',
  }
  opids = {v:k for k, v in opnames.items()}

  num_args = {
    isPower2:  1,
    isSignBit: 1,
    known:     2,
    maskZero:  2,
    NSWAdd:    2,
  }

  def __init__(self, op, args):
    assert 0 <= op < self.Last
    for i in range(len(args)):
      assert self.argAccepts(op, i+1, args[i])[0]
    self.op = op
    self.args = args
    if self.num_args[op] != len(args):
      raise ParseError('Wrong number of arguments (got %d, expected %d)' %\
                       (len(args), self.num_args[op]))

  def __repr__(self):
    args = [str(a) for a in self.args]
    return '%s(%s)' % (self.opnames[self.op], ', '.join(args))

  def getOpName(self):
    return self.opnames[self.op]

  @staticmethod
  def getOpId(name):
    try:
      return LLVMBoolPred.opids[name]
    except:
      raise ParseError('Unknown boolean predicate')

  arg_types = {
    isPower2:  ['const'],
    isSignBit: ['const'],
    known:     ['any', 'const'],
    maskZero:  ['input', 'const'],
    NSWAdd:    ['input', 'input'],
  }

  @staticmethod
  def argAccepts(op, arg, val):
    kind = LLVMBoolPred.arg_types[op][arg-1]
    if kind == 'any':
      return (True, 'any value')
    if kind == 'input':
      return (isinstance(val, (Input, Constant)), 'constant or input var')
    if kind == 'const':
      if isinstance(val, Input):
        ok = val.getName()[0] == 'C'
      else:
        ok = isinstance(val, Constant)
      return (ok, 'constant')
    assert False

  argConstraints = {
    isPower2:  lambda a: allTyEqual([a], Type.Int),
    isSignBit: lambda a: allTyEqual([a], Type.Int),
    known:     lambda a,b: allTyEqual([a,b], Type.Int),
    maskZero:  lambda a,b: allTyEqual([a,b], Type.Int),
    NSWAdd:    lambda a,b: allTyEqual([a,b], Type.Int),
  }

  def getTypeConstraints(self):
    c = self.argConstraints[self.op](*self.args)
    c += [v.getTypeConstraints() for v in self.args]
    return mk_and(c)

  def toSMT(self, state):
    args = [v.toSMT([], state, []) for v in self.args]
    return {
      self.isPower2:  lambda a: And(a != 0, a & (a-1) == 0),
      self.isSignBit: lambda a: a == (1 << (a.sort().size()-1)),
      self.known:     lambda a,b: a == b,
      self.maskZero:  lambda a,b: a & b == 0,
      self.NSWAdd:    lambda a,b: SignExt(1,a)+SignExt(1,b) == SignExt(1, a+b),
    }[self.op](*args)
