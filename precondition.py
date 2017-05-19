# Copyright 2014-2015 The Alive authors.
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
from codegen import *
from itertools import chain

class BoolPred:
  def fixupTypes(self, types):
    for attr in dir(self):
      a = getattr(self, attr)
      if isinstance(a, (Type, Value, BoolPred)):
        a.fixupTypes(types)
      if isinstance(a, tuple):
        for v in a:
          if isinstance(v, (Type, Value, BoolPred)):
            v.fixupTypes(types)


################################
class TruePred(BoolPred):
  def __repr__(self):
    return 'true'

  def getTypeConstraints(self):
    return BoolVal(True)

  def toSMT(self, state):
    return [], []

  def register_types(self, manager):
    pass

  def visit_pre(self, manager):
    return CVariable('true')


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
    d, v = self.v.toSMT(state)
    return d, [mk_not(mk_and(v))]

  def register_types(self, manager):
    self.v.register_types(manager)

  def visit_pre(self, manager):
    return CUnaryExpr('!', self.v.visit_pre(manager))

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
    d = []
    r = []
    for v in self.args:
      d2, v = v.toSMT(state)
      d += d2
      r += v
    return d, r

  def register_types(self, manager):
    for arg in self.args:
      arg.register_types(manager)

  def visit_pre(self, manager):
    return CBinExpr.reduce('&&', (arg.visit_pre(manager) for arg in self.args))

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
    d = []
    r = []
    for v in self.args:
      d2, v = v.toSMT(state)
      d += d2
      r.append(mk_and(v))
    return d, [mk_or(r)]

  def register_types(self, manager):
    for arg in self.args:
      arg.register_types(manager)

  def visit_pre(self, manager):
    return CBinExpr.reduce('||', (arg.visit_pre(manager) for arg in self.args))

################################
class BinaryBoolPred(BoolPred):
  EQ, NE, SLT, SLE, SGT, SGE, ULT, ULE, UGT, UGE, Last = range(11)

  opnames = ['==', '!=', '<', '<=', '>', '>=', 'u<', 'u<=', 'u>', 'u>=']

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
    defined = []
    v1 = self.v1.toSMT(defined, [], state, [])
    v2 = self.v2.toSMT(defined, [], state, [])
    return defined, [{
      self.EQ: lambda a,b: a == b,
      self.NE: lambda a,b: a != b,
      self.SLT: lambda a,b: a < b,
      self.SLE: lambda a,b: a <= b,
      self.SGT: lambda a,b: a > b,
      self.SGE: lambda a,b: a >= b,
      self.ULT: lambda a,b: ULT(a, b),
      self.ULE: lambda a,b: ULE(a, b),
      self.UGT: lambda a,b: UGT(a, b),
      self.UGE: lambda a,b: UGE(a, b),
    }[self.op](v1, v2)]

  gens = {
    EQ:  lambda a,b: CBinExpr('==', a, b),
    NE:  lambda a,b: CBinExpr('!=', a, b),
    SLT: lambda a,b: a.dot('slt', [b]),
    SLE: lambda a,b: a.dot('sle', [b]),
    SGT: lambda a,b: a.dot('sgt', [b]),
    SGE: lambda a,b: a.dot('sge', [b]),
    ULT: lambda a,b: a.dot('ult', [b]),
    ULE: lambda a,b: a.dot('ule', [b]),
    UGT: lambda a,b: a.dot('ugt', [b]),
    UGE: lambda a,b: a.dot('uge', [b]),
  }

  def register_types(self, manager):
    self.v1.register_types(manager)
    self.v2.register_types(manager)
    manager.unify(self.v1, self.v2)

  def visit_pre(self, manager):
    # FIXME: find less hacky way of comparing values of unconstrained types
    def untyped(op):
      return isinstance(op, ConstantVal) or \
        (isinstance(op, CnstFunction) and op.op in {CnstFunction.ctlz, CnstFunction.cttz, CnstFunction.log2, CnstFunction.width})

    if untyped(self.v1) and untyped(self.v2):
      cmp = {self.EQ: '==', self.NE: '!=', self.SLT: '<', self.SLE: '<=', self.SGT: '>',
             self.SGE: '>=', self.ULT: '<', self.ULE: '<=', self.UGT: '>', self.UGE: '>='}[self.op]
      return CBinExpr(cmp, self.v1.get_APInt_or_u64(manager), self.v2.get_APInt_or_u64(manager))

    return self.gens[self.op](self.v1.get_APInt(manager), self.v2.get_APInt_or_u64(manager))


################################
class LLVMBoolPred(BoolPred):
  eqptrs, isPower2, isPower2OrZ, isShiftedMask, isSignBit, maskZero,\
  NSWAdd, NUWAdd, NSWSub, NUWSub, NSWMul, NUWMul, NUWShl, OneUse,\
  Last = range(15)

  opnames = {
    eqptrs:      'equivalentAddressValues',
    isPower2:    'isPowerOf2',
    isPower2OrZ: 'isPowerOf2OrZero',
    isShiftedMask: 'isShiftedMask',
    isSignBit:   'isSignBit',
    maskZero:    'MaskedValueIsZero',
    NSWAdd:      'WillNotOverflowSignedAdd',
    NUWAdd:      'WillNotOverflowUnsignedAdd',
    NSWSub:      'WillNotOverflowSignedSub',
    NUWSub:      'WillNotOverflowUnsignedSub',
    NSWMul:      'WillNotOverflowSignedMul',
    NUWMul:      'WillNotOverflowUnsignedMul',
    NUWShl:      'WillNotOverflowUnsignedShl',
    OneUse:      'hasOneUse',
  }
  opids = {v:k for k, v in opnames.items()}

  num_args = {
    eqptrs:      2,
    isPower2:    1,
    isPower2OrZ: 1,
    isShiftedMask: 1,
    isSignBit:   1,
    maskZero:    2,
    NSWAdd:      2,
    NUWAdd:      2,
    NSWSub:      2,
    NUWSub:      2,
    NSWMul:      2,
    NUWMul:      2,
    NUWShl:      2,
    OneUse:      1,
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
    args = [a.getName() for a in self.args]
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
    eqptrs:      ['var', 'var'],
    isPower2:    ['any'],
    isPower2OrZ: ['any'],
    isShiftedMask: ['const'],
    isSignBit:   ['const'],
    maskZero:    ['input', 'const'],
    NSWAdd:      ['input', 'input'],
    NUWAdd:      ['input', 'input'],
    NSWSub:      ['input', 'input'],
    NUWSub:      ['input', 'input'],
    NSWMul:      ['input', 'input'],
    NUWMul:      ['input', 'input'],
    NUWShl:      ['const', 'const'],
    OneUse:      ['var'],
  }

  @staticmethod
  def argAccepts(op, arg, val):
    kind = LLVMBoolPred.arg_types[op][arg-1]
    if kind == 'any':
      return (True, 'any value')
    if kind == 'input':
      return (isinstance(val, (Input, Constant)), 'constant or input var')
    if kind == 'var':
      return (not isinstance(val, Constant), 'register')
    if kind == 'const':
      if isinstance(val, Input):
        ok = val.getName()[0] == 'C'
      else:
        ok = isinstance(val, Constant)
      return (ok, 'constant')
    assert False

  argConstraints = {
    eqptrs:      lambda a,b: allTyEqual([a,b], Type.Ptr),
    isPower2:    lambda a: allTyEqual([a], Type.Int),
    isPower2OrZ: lambda a: allTyEqual([a], Type.Int),
    isShiftedMask: lambda a: allTyEqual([a], Type.Int),
    isSignBit:   lambda a: allTyEqual([a], Type.Int),
    maskZero:    lambda a,b: allTyEqual([a,b], Type.Int),
    NSWAdd:      lambda a,b: allTyEqual([a,b], Type.Int),
    NUWAdd:      lambda a,b: allTyEqual([a,b], Type.Int),
    NSWSub:      lambda a,b: allTyEqual([a,b], Type.Int),
    NUWSub:      lambda a,b: allTyEqual([a,b], Type.Int),
    NSWMul:      lambda a,b: allTyEqual([a,b], Type.Int),
    NUWMul:      lambda a,b: allTyEqual([a,b], Type.Int),
    NUWShl:      lambda a,b: allTyEqual([a,b], Type.Int),
    OneUse:      lambda a: []
  }

  def getTypeConstraints(self):
    c = self.argConstraints[self.op](*self.args)
    c += [v.getTypeConstraints() for v in self.args]
    return mk_and(c)

  def _mkMustAnalysis(self, d, vars, expr):
    # If all vars are constant, then analysis is precise.
    if all(str(v)[0] == 'C' for v in vars):
      return d, [expr]
    c = BitVec('ana_%s' % self, 1)
    return d + [Implies(c == 1, expr)], [c == 1]

  def toSMT(self, state):
    d = []
    args = []
    for v in self.args:
      a = v.toSMT(d, [], state, [])
      args.append(a)

    return {
      self.eqptrs:      lambda a,b: self._mkMustAnalysis(d, [a,b], a == b),
      self.isPower2:    lambda a: self._mkMustAnalysis(d, [a],
                          And(a != 0, a & (a-1) == 0)),
      self.isPower2OrZ: lambda a: self._mkMustAnalysis(d, [a], a & (a-1) == 0),
      self.isShiftedMask: lambda a: (d, isShiftedMask(a)),
      self.isSignBit:   lambda a: (d, [a == (1 << (a.sort().size()-1))]),
      self.maskZero:    lambda a,b: self._mkMustAnalysis(d, [a], a & b == 0),
      self.NSWAdd:      lambda a,b: self._mkMustAnalysis(d, [a,b],
                          SignExt(1,a) + SignExt(1,b) == SignExt(1, a+b)),
      self.NUWAdd:      lambda a,b: self._mkMustAnalysis(d, [a,b],
                          ZeroExt(1,a)+ZeroExt(1,b) == ZeroExt(1, a+b)),
      self.NSWSub:      lambda a,b: self._mkMustAnalysis(d, [a,b],
                          SignExt(1,a)-SignExt(1,b) == SignExt(1, a-b)),
      self.NUWSub:      lambda a,b: self._mkMustAnalysis(d, [a,b],
                          ZeroExt(1,a)-ZeroExt(1,b) == ZeroExt(1, a-b)),
      self.NSWMul:      lambda a,b: self._mkMustAnalysis(d, [a,b],
                          no_overflow_smul(a, b)),
      self.NUWMul:      lambda a,b: self._mkMustAnalysis(d, [a,b],
                          no_overflow_umul(a, b)),
      self.NUWShl:      lambda a,b: (d, [LShR(a << b, b) == a]),
      self.OneUse:      lambda a: (d,
                          [get_users_var(self.args[0].getUniqueName()) == 1]),
    }[self.op](*args)

  def register_types(self, manager):
    for arg in self.args:
      arg.register_types(manager)

    if self.op in {LLVMBoolPred.maskZero, LLVMBoolPred.NSWAdd}:
      manager.unify(self.args[0], self.args[1])

  def visit_pre(self, manager):
    #TODO: reduce use of Alive-specific functions in generated code
    # e.g., WillNotOverflow* mul/shl

    if self.op == LLVMBoolPred.eqptrs:
      raise AliveError('eqptrs not currently supported')

    if self.op == LLVMBoolPred.isPower2:
      a = self.args[0]
      if isinstance(a, Constant):
        return a.get_APInt(manager).dot('isPowerOf2', [])

      return CFunctionCall('isKnownToBeAPowerOfTwo', manager.get_cexp(a),
        CVariable('DL'))

    if self.op == LLVMBoolPred.isPower2OrZ:
      return CFunctionCall('isKnownToBeAPowerOfTwo',
        manager.get_cexp(self.args[0]), CVariable('DL'), CVariable('true'))

    if self.op == LLVMBoolPred.NUWAdd:
      return CBinExpr('==',
        CFunctionCall('computeOverflowForUnsignedAdd',
          manager.get_cexp(self.args[0]),
          manager.get_cexp(self.args[1]),
          CVariable('I')),
        CVariable('OverflowResult::NeverOverflows'))

    if self.op == LLVMBoolPred.NUWMul:
      return CBinExpr('==',
        CFunctionCall('computeOverflowForUnsignedMul',
          manager.get_cexp(self.args[0]),
          manager.get_cexp(self.args[1]),
          CVariable('I')),
        CVariable('OverflowResult::NeverOverflows'))

    if self.op == LLVMBoolPred.NSWMul:
      return CFunctionCall(self.opnames[self.op], 
        manager.get_cexp(self.args[0]),
        manager.get_cexp(self.args[1]),
        CVariable('*I'))

    opname = LLVMBoolPred.opnames[self.op]
    args = []
    for i in range(self.num_args[self.op]):
      if self.arg_types[self.op][i] == 'const':
        args.append(self.args[i].get_APInt(manager))
      else:
        args.append(manager.get_cexp(self.args[i]))

    if self.op == LLVMBoolPred.isShiftedMask:
      return args[0].dot(LLVMBoolPred.opnames[self.op], [])

    if self.op == LLVMBoolPred.isSignBit:
      return args[0].dot('isSignMask', [])

    if self.op == LLVMBoolPred.OneUse:
      return args[0].arr('hasOneUse', [])

    if self.op in {LLVMBoolPred.NSWAdd, LLVMBoolPred.NSWSub,
        LLVMBoolPred.NUWSub}:
      return CFunctionCall(self.opnames[self.op], args[0], args[1], CVariable('*I'))
      # TODO: obtain root from manager?

    return CFunctionCall(self.opnames[self.op], *args)
