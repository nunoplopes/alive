# Copyright 2014-2016 The Alive authors.
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

from value import *
from codegen import *


class Constant(Value):
  def mk_name(self):
    self.setName(str(self))
    self.id = mk_unique_id()
    self.type.setName(self.getName() + '_' + self.id)

  def getUniqueName(self):
    return self.getName() + '_' + self.id

  def isConst(self):
    return True

  def get_APInt(self, manager):
    return CFunctionCall('APInt',
      manager.get_llvm_type(self).arr('getScalarSizeInBits', []), #TODO: add to manager API?
      self.get_APInt_or_u64(manager))

  def get_Value(self, manager):
    return CFunctionCall('ConstantInt::get',
      manager.get_llvm_type(self),
      self.get_APInt_or_u64(manager))


################################
class ConstantVal(Constant):
  def __init__(self, val, type):
    assert isinstance(type, Type)
    self.val = val
    self.type = type
    self.mk_name()

  def __repr__(self):
    if isinstance(self.type, PtrType) and self.val == 0:
      return 'null'
    if isinstance(self.type, IntType) and self.type.defined and\
       self.type.getSize() == 1:
      return 'true' if self.val == 1 else 'false'
    return str(self.val)

  def getTypeConstraints(self):
    c = self.type.getTypeConstraints()
    if self.val != 0 and not self.type.defined:
      return And(c, self.type >= self.val.bit_length())
    return c

  def toSMT(self, defined, state, qvars):
    return BitVecVal(self.val, self.type.getSize()), BoolVal(True)

  def register_types(self, manager):
    if isinstance(self.type, PtrType):
      manager.register_type(self, self.type, PtrType())
    else:
      manager.register_type(self, self.type, IntType())

  def get_APInt_or_u64(self, manager):
    return CVariable(str(self.val))

################################
class PoisonVal(Constant):
  def __init__(self, type):
    assert isinstance(type, Type)
    self.type = type
    self.mk_name()

  def __repr__(self):
    return 'poison'

  def getTypeConstraints(self):
    return self.type.getTypeConstraints()

  def toSMT(self, defined, state, qvars):
    return BitVecVal(0, self.type.getSize()), BoolVal(False)


class UndefVal(Constant):
  def __init__(self, type):
    assert isinstance(type, Type)
    self.type = type
    self.mk_name()

  def __repr__(self):
    return 'undef'

  def getTypeConstraints(self):
    return self.type.getTypeConstraints()

  def toSMT(self, defined, state, qvars):
    var = BitVec(self.getUniqueName(), self.type.getSize())
    qvars.append(var)
    return var, BoolVal(True)


################################
class CnstUnaryOp(Constant):
  Not, Neg, Last = range(3)

  opnames = ['~', '-']

  def __init__(self, op, v):
    assert 0 <= op < self.Last
    assert isinstance(v, (Constant, Input))
    self.op = op
    self.v = v
    self.type = IntType()
    self.mk_name()

  def __repr__(self):
    return '%s%s' % (self.opnames[self.op], self.v)

  @staticmethod
  def getOpId(name):
    for i in range(CnstUnaryOp.Last):
      if CnstUnaryOp.opnames[i] == name:
        return i
    assert False

  def getType(self):
    return self.v.getType()

  def getTypeConstraints(self):
    return mk_and([self.type == self.v.type,
                   self.v.getTypeConstraints(),
                   self.type.getTypeConstraints()])

  def toSMT(self, defined, state, qvars):
    v, u = self.v.toSMT(defined, state, qvars)
    assert is_true(u)
    return {
      self.Not: lambda a: ~a,
      self.Neg: lambda a: -a,
    }[self.op](v), BoolVal(True)

  def register_types(self, manager):
    self.v.register_types(manager)
    manager.register_type(self, self.type, IntType())
    manager.unify(self, self.v)

  def get_APInt_or_u64(self, manager):
    return CUnaryExpr(self.opnames[self.op], self.v.get_APInt_or_u64(manager))

  def get_APInt(self, manager):
    return CUnaryExpr(self.opnames[self.op], self.v.get_APInt(manager))


################################
class CnstBinaryOp(Constant):
  And, Or, Xor, Add, Sub, Mul, Div, DivU, Rem, RemU, AShr, LShr, Shl,\
  Last = range(14)

  opnames = ['&', '|', '^', '+', '-', '*', '/', '/u', '%', '%u','>>','u>>','<<']

  def __init__(self, op, v1, v2):
    assert 0 <= op < self.Last
    assert isinstance(v1, (Constant, Input))
    assert isinstance(v2, (Constant, Input))
    self.op = op
    self.v1 = v1
    self.v2 = v2
    self.type = IntType()
    self.mk_name()

  def __repr__(self):
    return '(%s %s %s)' % (self.v1, self.opnames[self.op], self.v2)

  @staticmethod
  def getOpId(name):
    for i in range(CnstBinaryOp.Last):
      if CnstBinaryOp.opnames[i] == name:
        return i
    assert False

  def getTypeConstraints(self):
    return mk_and([self.type == self.v1.type,
                   self.type == self.v2.type,
                   self.v1.getTypeConstraints(),
                   self.v2.getTypeConstraints(),
                   self.type.getTypeConstraints()])

  def toSMT(self, defined, state, qvars):
    v1, u1 = self.v1.toSMT(defined, state, qvars)
    v2, u2 = self.v2.toSMT(defined, state, qvars)
    assert is_true(u1) and is_true(u2)
    return {
      self.And:  lambda a,b: a & b,
      self.Or:   lambda a,b: a | b,
      self.Xor:  lambda a,b: a ^ b,
      self.Add:  lambda a,b: a + b,
      self.Sub:  lambda a,b: a - b,
      self.Mul:  lambda a,b: a * b,
      self.Div:  lambda a,b: a / b,
      self.DivU: lambda a,b: UDiv(a, b),
      self.Rem:  lambda a,b: SRem(a, b),
      self.RemU: lambda a,b: URem(a, b),
      self.AShr: lambda a,b: a >> b,
      self.LShr: lambda a,b: LShR(a, b),
      self.Shl:  lambda a,b: a << b,
    }[self.op](v1, v2), BoolVal(True)

  def register_types(self, manager):
    self.v1.register_types(manager)
    self.v2.register_types(manager)
    manager.register_type(self, self.type, IntType())
    manager.unify(self, self.v1, self.v2)

  def get_APInt_or_u64(self, manager):
    return self.get_APInt(manager)

  _cfun = {
      And:  lambda a,b: CBinExpr('&', a, b),
      Or:   lambda a,b: CBinExpr('|', a, b),
      Xor:  lambda a,b: CBinExpr('^', a, b),
      Add:  lambda a,b: CBinExpr('+', a, b),
      Sub:  lambda a,b: CBinExpr('-', a, b),
      Mul:  lambda a,b: CBinExpr('*', a, b),
      Div:  lambda a,b: a.dot('sdiv', [b]),
      DivU: lambda a,b: a.dot('udiv', [b]),
      Rem:  lambda a,b: a.dot('srem', [b]),
      RemU: lambda a,b: a.dot('urem', [b]),
      AShr: lambda a,b: a.dot('ashr', [b]),
      LShr: lambda a,b: a.dot('lshr', [b]),
      Shl:  lambda a,b: CBinExpr('<<', a,  b),
    }

  _overloaded_rhs = {Add, Sub, AShr, LShr, Shl}

  def get_APInt(self, manager):
    op = CnstBinaryOp._cfun[self.op]

    if self.op in CnstBinaryOp._overloaded_rhs:
      return op(self.v1.get_APInt(manager), self.v2.get_APInt_or_u64(manager))

    return op(self.v1.get_APInt(manager), self.v2.get_APInt(manager))


################################
class CnstFunction(Constant):
  abs, sbits, obits, zbits, ctlo, ctlz, cttz, ctto, log2, lshr, max, sext, \
  trunc, umax, umin, width, zext, Last = range(18)

  opnames = {
    abs:   'abs',
    sbits: 'ComputeNumSignBits',
    obits: 'computeKnownOneBits',
    zbits: 'computeKnownZeroBits',
    ctlo:  'countLeadingOnes',
    ctlz:  'countLeadingZeros',
    cttz:  'countTrailingZeros',
    ctto:  'countTrailingOnes',
    log2:  'log2',
    lshr:  'lshr',
    max:   'max',
    sext:  'sext',
    trunc: 'trunc',
    umax:  'umax',
    umin:  'umin',
    width: 'width',
    zext:  'zext',
  }
  opids = {v:k for k,v in opnames.items()}

  num_args = {
    abs:   1,
    sbits: 1,
    obits: 1,
    zbits: 1,
    ctlo:  1,
    ctlz:  1,
    cttz:  1,
    ctto:  1,
    log2:  1,
    lshr:  2,
    max:   2,
    sext:  1,
    trunc: 1,
    umax:  2,
    umin:  2,
    width: 1,
    zext:  1,
  }

  def __init__(self, op, args, type):
    assert 0 <= op < self.Last
    for a in args:
      assert isinstance(a, Value)
    assert isinstance(type, IntType)

    self.op = op
    self.args = args
    self.type = type
    self.mk_name()

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
    if name in CnstFunction.opids:
      return CnstFunction.opids[name]
    raise ParseError('Unknown function:')

  def getTypeConstraints(self):
    c = {
      self.abs:   lambda a: allTyEqual([a,self], Type.Int),
      self.sbits: lambda a: allTyEqual([a], Type.Int),
      self.obits: lambda a: allTyEqual([a,self], Type.Int),
      self.zbits: lambda a: allTyEqual([a,self], Type.Int),
      self.ctlo:  lambda a: allTyEqual([a], Type.Int),
      self.ctlz:  lambda a: allTyEqual([a], Type.Int),
      self.cttz:  lambda a: allTyEqual([a], Type.Int),
      self.ctto:  lambda a: allTyEqual([a], Type.Int),
      self.log2:  lambda a: allTyEqual([a], Type.Int),
      self.lshr:  lambda a,b: allTyEqual([a,b,self], Type.Int),
      self.max:   lambda a,b: allTyEqual([a,b,self], Type.Int),
      self.sext:  lambda a: [a.type < self.type],
      self.trunc: lambda a: [self.type < a.type],
      self.umax:  lambda a,b: allTyEqual([a,b,self], Type.Int),
      self.umin:  lambda a,b: allTyEqual([a,b,self], Type.Int),
      self.width: lambda a: [],
      self.zext:  lambda a: [self.type > a.type],
    }[self.op](*self.args)

    return mk_and([v.getTypeConstraints() for v in self.args] +\
                  [self.type.getTypeConstraints()] + c)

  def toSMT(self, defined, state, qvars):
    size = self.type.getSize()
    args = []
    for v in self.args:
      a, u = v.toSMT(defined, state, qvars)
      defined.append(u)
      args.append(a)

    d, v = {
      self.abs:   lambda a: ([], If(a >= 0, a, -a)),
      self.sbits: lambda a:
        (lambda b: ([ULE(b, ComputeNumSignBits(a, size))], b))
          (ComputeNumSignBits(BitVec('ana_' + self.getName(), size), size)),
      self.obits: lambda a: (lambda b: ([b & ~a == 0], b))
                              (BitVec('ana_' + self.getName(), size)),
      self.zbits: lambda a: (lambda b: ([b & a == 0], b))
                              (BitVec('ana_' + self.getName(), size)),
      self.ctlo:  lambda a: ([], count_leading(a, 1, size)),
      self.ctlz:  lambda a: ([], count_leading(a, 0, size)),
      self.cttz:  lambda a: ([], cttz(a, size)),
      self.ctto:  lambda a: ([], cttz(~a, size)),
      self.log2:  lambda a: ([], bv_log2(a, size)),
      self.lshr:  lambda a,b: ([], LShR(a, b)),
      self.max:   lambda a,b: ([], If(a > b, a, b)),
      self.sext:  lambda a: ([], SignExt(size - a.size(), a)),
      self.trunc: lambda a: ([], Extract(size-1, 0, a)),
      self.umax:  lambda a,b: ([], If(UGT(a,b), a, b)),
      self.umin:  lambda a,b: ([], If(ULE(a,b), a, b)),
      self.width: lambda a: (None, BitVecVal(a.size(), size)),
      self.zext:  lambda a: ([], ZeroExt(size - a.size(), a)),
    }[self.op](*args)

    if d is None:
      del defined[:]
    else:
      defined += d
    return v, BoolVal(True)

  def register_types(self, manager):
    for arg in self.args:
      arg.register_types(manager)

    manager.register_type(self, self.type, IntType())

    if self.op in {CnstFunction.abs, CnstFunction.obits, CnstFunction.zbits}:
      manager.unify(self, self.args[0])

    elif self.op in {CnstFunction.lshr, CnstFunction.max, CnstFunction.umax}:
      manager.unify(self, self.args[0], self.args[1])

  def _get_cexp(self, manager):
    if self.op == CnstFunction.abs:
      return False, self.args[0].get_APInt(manager).dot('abs', [])

    if self.op == CnstFunction.sbits:
      return True, CFunctionCall('ComputeNumSignBits', manager.get_cexp(self.args[0]))

    if self.op == CnstFunction.obits:
      return False, CFunctionCall('computeKnownOneBits', manager.get_cexp(self.args[0]))

    if self.op == CnstFunction.zbits:
      return False, CFunctionCall('computeKnownZeroBits', manager.get_cexp(self.args[0]))

    if self.op == CnstFunction.ctlz:
      return True, self.args[0].get_APInt(manager).dot('countLeadingZeros', [])

    if self.op == CnstFunction.cttz:
      return True, self.args[0].get_APInt(manager).dot('countTrailingZeros', [])

    if self.op == CnstFunction.log2:
      return True, self.args[0].get_APInt(manager).dot('logBase2', [])

    if self.op == CnstFunction.lshr:
      return False, self.args[0].get_APInt(manager).dot('lshr',
        [self.args[1].get_APInt_or_u64(manager)])

    if self.op == CnstFunction.max:
      return False, CFunctionCall('APIntOps::smax',
        self.args[0].get_APInt(manager), self.args[1].get_APInt(manager))

    if self.op == CnstFunction.sext:
      return False, self.args[0].get_APInt(manager).dot('sext',
        [manager.get_llvm_type(self).arr('getScalarSizeInBits', [])])

    if self.op == CnstFunction.trunc:
      return False, self.args[0].get_APInt(manager).dot('trunc',
        [manager.get_llvm_type(self).arr('getScalarSizeInBits', [])])

    if self.op == CnstFunction.umax:
      return False, CFunctionCall('APIntOps::umax', 
        self.args[0].get_APInt(manager), self.args[1].get_APInt(manager))

    if self.op == CnstFunction.width:
      return True, manager.get_llvm_type(self.args[0]).arr('getScalarSizeInBits', [])

    if self.op == CnstFunction.zext:
      return False, self.args[0].get_APInt(manager).dot('zext', 
        [manager.get_llvm_type(self).arr('getScalarSizeInBits',[])])

    raise AliveError(self.opnames[self.op] + ' not implemented')

  def get_APInt(self, manager):
    wrap, cexp = self._get_cexp(manager)
    if wrap:
      return CFunctionCall('APInt', 
        manager.get_llvm_type(self).arr('getScalarSizeInBits',[]), cexp)

    return cexp
    return self.get_Value(manager).arr('getValue',[])

  def get_APInt_or_u64(self, manager):
    return self._get_cexp(manager)[1]
