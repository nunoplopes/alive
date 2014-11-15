# Copyright 2014 The Alive authors.
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
  
  def getCName(self):
    raise AliveError('Called getCName on constant {}'.format(self.getUniqueName()))

  def getLabel(self):
    return self.id

  def toAPInt(self):
    return CTest('<APInt>')

  def toOperand(self):
    return CFunctionCall('ConstantInt::get', self.toCType(), self.toAPIntOrLit())

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

  def isConst(self):
    return True

  def getTypeConstraints(self):
    c = self.type.getTypeConstraints()
    if self.val != 0 and not self.type.defined:
      # One more bit for positive integers to allow for sign bit.
      bits = self.val.bit_length() + int(self.val >= 0)
      return And(c, self.type >= bits)
    return c

  def toSMT(self, defined, poison, state, qvars):
    return BitVecVal(self.val, self.type.getSize())

  def toOperand(self):
    return CFunctionCall('ConstantInt::get', self.toCType(), CVariable(str(self.val)))
    # NOTE: address sign for >64-bit ints

  def toAPInt(self):
    # FIXME: ensure value is integral

    return CFunctionCall('APInt',
      self.toCType().arr('getScalarSizeInBits', []),
      CVariable(self.val))

  def toAPIntOrLit(self):
    return CVariable(str(self.val))

  def setRepresentative(self, manager):
    self._manager = manager
    manager.add_label(self.getLabel(), self.type, anon=True)
    # TODO: handle non-integers?

################################
class UndefVal(Constant):
  def __init__(self, type):
    assert isinstance(type, Type)
    self.type = type
    self.mk_name()

  def __repr__(self):
    return 'undef'

  def getTypeConstraints(self):
    # overload Constant's method
    return self.type.getTypeConstraints()

  def toSMT(self, defined, poison, state, qvars):
    v = BitVec('undef' + self.id, self.type.getSize())
    qvars += [v]
    return v

  def setRepresentative(self, manager):
    # FIXME: handle defined types
    self._manager = manager
    manager.add_label(self.getLabel(), self.type, anon=True)

  def toAPInt(self):
    raise AliveError("Can't represent undef as APInt")

  def toOperand(self):
    return CFunctionCall('UndefValue::get', self.toCType())

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

  def toSMT(self, defined, poison, state, qvars):
    v = self.v.toSMT(defined, poison, state, qvars)
    return {
      self.Not: lambda a: ~a,
      self.Neg: lambda a: -a,
    }[self.op](v)

  def toAPInt(self):
    return CUnaryExpr(self.opnames[self.op], self.v.toAPInt())

  def setRepresentative(self, manager):
    self._manager = manager
    self.v.setRepresentative(manager)
    manager.add_label(self.getLabel(), self.type, anon=True)
    manager.unify(self.getLabel(), self.v.getLabel())


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

  def toSMT(self, defined, poison, state, qvars):
    v1 = self.v1.toSMT(defined, poison, state, qvars)
    v2 = self.v2.toSMT(defined, poison, state, qvars)
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
    }[self.op](v1, v2)

  def toOperand(self):
    if self.op == self.Or:
      return CFunctionCall('ConstantExpr::getOr', self.v1.toOperand(), self.v2.toOperand())

    return Constant.toOperand(self)

  def toAPInt(self):
    op = {
      CnstBinaryOp.And:  lambda a,b: CBinExpr('&', a, b),
      CnstBinaryOp.Or:   lambda a,b: CBinExpr('|', a, b),
      CnstBinaryOp.Xor:  lambda a,b: CBinExpr('^', a, b),
      CnstBinaryOp.Add:  lambda a,b: CBinExpr('+', a, b),
      CnstBinaryOp.Sub:  lambda a,b: CBinExpr('-', a, b),
      CnstBinaryOp.Mul:  lambda a,b: CBinExpr('*', a, b),
      CnstBinaryOp.Div:  lambda a,b: a.dot('sdiv', [b]),
      CnstBinaryOp.DivU: lambda a,b: a.dot('udiv', [b]),
      CnstBinaryOp.Rem:  lambda a,b: a.dot('srem', [b]),
      CnstBinaryOp.RemU: lambda a,b: a.dot('urem', [b]),
      CnstBinaryOp.AShr: lambda a,b: a.dot('ashr', [b]),
      CnstBinaryOp.LShr: lambda a,b: a.dot('lshr', [b]),
      CnstBinaryOp.Shl:  lambda a,b: CBinExpr('<<', a,  b),
    }[self.op]

    if self.op in {CnstBinaryOp.Add, CnstBinaryOp.Sub, CnstBinaryOp.AShr, CnstBinaryOp.LShr, CnstBinaryOp.Shl}:
      return op(self.v1.toAPInt(), self.v2.toAPIntOrLit())

    return op(self.v1.toAPInt(), self.v2.toAPInt())

  def setRepresentative(self, manager):
    self._manager = manager
    self.v1.setRepresentative(manager)
    self.v2.setRepresentative(manager)
    manager.add_label(self.getLabel(), self.type, anon=True)
    manager.unify(self.getLabel(), self.v1.getLabel(), self.v2.getLabel())

################################
class CnstFunction(Constant):
  abs, sbits, obits, zbits, ctlz, cttz, log2, lshr, max, sext, trunc, umax,\
  width, zext, Last = range(15)

  opnames = {
    abs:   'abs',
    sbits: 'ComputeNumSignBits',
    obits: 'computeKnownOneBits',
    zbits: 'computeKnownZeroBits',
    ctlz:  'countLeadingZeros',
    cttz:  'countTrailingZeros',
    log2:  'log2',
    lshr:  'lshr',
    max:   'max',
    sext:  'sext',
    trunc: 'trunc',
    umax:  'umax',
    width: 'width',
    zext:  'zext',
  }
  opids = {v:k for k,v in opnames.items()}

  num_args = {
    abs:   1,
    sbits: 1,
    obits: 1,
    zbits: 1,
    ctlz:  1,
    cttz:  1,
    log2:  1,
    lshr:  2,
    max:   2,
    sext:  1,
    trunc: 1,
    umax:  2,
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
      self.ctlz:  lambda a: allTyEqual([a], Type.Int),
      self.cttz:  lambda a: allTyEqual([a], Type.Int),
      self.log2:  lambda a: allTyEqual([a], Type.Int),
      self.lshr:  lambda a,b: allTyEqual([a,b,self], Type.Int),
      self.max:   lambda a,b: allTyEqual([a,b,self], Type.Int),
      self.sext:  lambda a: [a.type < self.type],
      self.trunc: lambda a: [self.type < a.type],
      self.umax:  lambda a,b: allTyEqual([a,b,self], Type.Int),
      self.width: lambda a: [],
      self.zext:  lambda a: [self.type > a.type],
    }[self.op](*self.args)

    return mk_and([v.getTypeConstraints() for v in self.args] +\
                  [self.type.getTypeConstraints()] + c)

  def toSMT(self, defined, poison, state, qvars):
    size = self.type.getSize()
    args = []
    for v in self.args:
      a = v.toSMT(defined, poison, state, qvars)
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
      self.ctlz:  lambda a: ([], ctlz(a, size)),
      self.cttz:  lambda a: ([], cttz(a, size)),
      self.log2:  lambda a: ([], bv_log2(a, size)),
      self.lshr:  lambda a,b: ([], LShR(a, b)),
      self.max:   lambda a,b: ([], If(a > b, a, b)),
      self.sext:  lambda a: ([], SignExt(size - a.size(), a)),
      self.trunc: lambda a: ([], Extract(size-1, 0, a)),
      self.umax:  lambda a,b: ([], If(UGT(a,b), a, b)),
      self.width: lambda a: (None, BitVecVal(a.size(), size)),
      self.zext:  lambda a: ([], ZeroExt(size - a.size(), a)),
    }[self.op](*args)

    if d is None:
      del defined[:]
    else:
      defined += d
    return v

  def _toCExpr(self):
    if self.op == CnstFunction.abs:
      return False, self.args[0].toAPInt().dot('abs', [])

    if self.op == CnstFunction.sbits:
      return True, CFunctionCall('ComputeNumSignBits', self.args[0].toOperand())

    if self.op == CnstFunction.obits:
      return False, CFunctionCall('computeKnownOneBits', self.args[0].toOperand())

    if self.op == CnstFunction.zbits:
      return False, CFunctionCall('computeKnownZeroBits', self.args[0].toOperand())

    if self.op == CnstFunction.ctlz:
      return True, self.args[0].toAPInt().dot('countLeadingZeros', [])

    if self.op == CnstFunction.cttz:
      return True, self.args[0].toAPInt().dot('countTrailingZeros', [])

    if self.op == CnstFunction.log2:
      return True, self.args[0].toAPInt().dot('logBase2', [])

    if self.op == CnstFunction.lshr:
      return False, self.args[0].toAPInt().dot('lshr', [self.args[1].toAPIntOrLit()])

    if self.op == CnstFunction.max:
      return False, CFunctionCall('APIntOps::smax', self.args[0].toAPInt(), self.args[1].toAPInt())

    if self.op == CnstFunction.sext:
      return False, self.args[0].toAPInt().dot('sext', [self.toCType().arr('getScalarSizeInBits',[])])

    if self.op == CnstFunction.trunc:
      return False, self.args[0].toAPInt().dot('trunc', [self.toCType().arr('getScalarSizeInBits',[])])

    if self.op == CnstFunction.umax:
      return False, CFunctionCall('APIntOps::umax', self.args[0].toAPInt(), self.args[1].toAPInt())

    if self.op == CnstFunction.width:
      return True, self.args[0].toCType().arr('getScalarSizeInBits', [])

    if self.op == CnstFunction.zext:
      return False, self.args[0].toAPInt().dot('zext', [self.toCType().arr('getScalarSizeInBits',[])])

    raise AliveError(self.opnames[self.op] + ' not implemented')

  def toAPInt(self):
    wrap, cexpr = self._toCExpr()
    if wrap:
      return CFunctionCall('APInt', self.toCType().arr('getScalarSizeInBits',[]), cexpr)

    return cexpr

  def toAPIntOrLit(self):
    _, cexpr = self._toCExpr()
    return cexpr

  def setRepresentative(self, manager):
    self._manager = manager
    manager.add_label(self.getLabel(), self.type, anon=True)

    for arg in self.args:
      arg.setRepresentative(manager)

    if self.op == self.abs or self.op == CnstFunction.obits or self.op == CnstFunction.zbits:
      manager.unify(self.getLabel(), self.args[0].getLabel())

    elif self.op == self.lshr or self.op == self.max or self.op == self.umax:
      manager.unify(self.getLabel(), self.args[0].getLabel(), self.args[1].getLabel())
