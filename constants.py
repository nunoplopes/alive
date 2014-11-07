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

  def toSMT(self, poison, state, qvars):
    return [], BitVecVal(self.val, self.type.getSize())

  def toOperand(self):
    return CFunctionCall('ConstantInt::get', self.toCType(), CVariable(str(self.val)))
    # NOTE: address sign for >64-bit ints

  def toAPInt(self):
    # FIXME: ensure value is integral

    return CFunctionCall('APInt',
      self.toCType().arr('getPrimitiveSizeInBits', []),
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

  def toSMT(self, poison, state, qvars):
    v = BitVec('undef' + self.id, self.type.getSize())
    qvars += [v]
    return [], v

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

  def toSMT(self, poison, state, qvars):
    return [], {
      self.Not: lambda a: ~a,
      self.Neg: lambda a: -a,
    }[self.op](self.v.toSMT(poison, state, qvars)[1])

  def toAPInt(self):
    return CUnaryExpr(self.opnames[self.op], self.v.toAPInt())

  def setRepresentative(self, manager):
    self._manager = manager
    self.v.setRepresentative(manager)
    manager.add_label(self.getLabel(), self.type, anon=True)
    manager.unify(self.getLabel(), self.v.getLabel())


################################
class CnstBinaryOp(Constant):
  And, Or, Xor, Add, Sub, Mul, Div, Rem, Shr, Shl, Last = range(11)

  opnames = ['&', '|', '^', '+', '-', '*', '/', '%', '>>', '<<']

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

  def toSMT(self, poison, state, qvars):
    v1 = self.v1.toSMT(poison, state, qvars)[1]
    v2 = self.v2.toSMT(poison, state, qvars)[1]
    return [], {
      self.And: lambda a,b: a & b,
      self.Or:  lambda a,b: a | b,
      self.Xor: lambda a,b: a ^ b,
      self.Add: lambda a,b: a + b,
      self.Sub: lambda a,b: a - b,
      self.Mul: lambda a,b: a * b,
      self.Div: lambda a,b: a / b,
      self.Rem: lambda a,b: SRem(a, b),
      self.Shr: lambda a,b: a >> b,
      self.Shl: lambda a,b: a << b,
    }[self.op](v1, v2)

  def toOperand(self):
    if self.op == self.Or:
      return CFunctionCall('ConstantExpr::getOr', self.v1.toOperand(), self.v2.toOperand())

    return Constant.toOperand(self)

  def toAPInt(self):
    if self.op == self.Shr:
      return self.v1.toAPInt().dot('ashr', [self.v2.toAPIntOrLit()])
    if self.op == self.Div:
      return self.v1.toAPInt().dot('sdiv', [self.v2.toAPInt()])
    if self.op == self.Rem:
      return self.v1.toAPInt().dot('srem', [self.v2.toAPInt()])

    if self.op in {self.Add, self.Sub, self.Shl}:
      return CBinExpr(self.opnames[self.op], self.v1.toAPInt(), self.v2.toAPIntOrLit())

    return CBinExpr(self.opnames[self.op], self.v1.toAPInt(), self.v2.toAPInt())

  def setRepresentative(self, manager):
    self._manager = manager
    self.v1.setRepresentative(manager)
    self.v2.setRepresentative(manager)
    manager.add_label(self.getLabel(), self.type, anon=True)
    manager.unify(self.getLabel(), self.v1.getLabel(), self.v2.getLabel())

################################
class CnstFunction(Constant):
  abs, lshr, trunc, umax, width, Last = range(6)

  opnames = {
    abs:   'abs',
    lshr:  'lshr',
    trunc: 'trunc',
    umax:  'umax',
    width: 'width',
  }
  opids = {v:k for k,v in opnames.items()}

  num_args = {
    abs:   1,
    lshr:  2,
    trunc: 1,
    umax:  2,
    width: 1,
  }

  def __init__(self, op, args, type):
    assert 0 <= op < self.Last
    for a in args:
      assert isinstance(a, Value)

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
      self.lshr:  lambda a,b: allTyEqual([a,b,self], Type.Int),
      self.trunc: lambda a: [self.type < a.type],
      self.umax:  lambda a,b: allTyEqual([a,b,self], Type.Int),
      self.width: lambda a: [],
    }[self.op](*self.args)

    return mk_and([v.getTypeConstraints() for v in self.args] +\
                  [self.type.getTypeConstraints()] + c)

  def toSMT(self, poison, state, qvars):
    args = [v.toSMT(poison, state, qvars)[1] for v in self.args]
    return [], {
      self.abs:   lambda a: If(a >= 0, a, -a),
      self.lshr:  lambda a,b: LShR(a,b),
      self.trunc: lambda a: Extract(self.type.getSize()-1, 0, a),
      self.umax:  lambda a,b: If(UGT(a,b), a, b),
      self.width: lambda a: BitVecVal(a.sort().size(), self.type.getSize()),
    }[self.op](*args)

  def toAPInt(self):
    if self.op == self.abs:
      return self.args[0].toAPInt().dot('abs', [])

    if self.op == self.lshr:
      return self.args[0].toAPInt().dot('lshr', [self.args[1].toAPIntOrLit()])

    if self.op == self.trunc:
      return self.args[0].toAPInt().dot('trunc', [self.toCType().arr('getPrimitiveSizeInBits',[])])

    if self.op == self.umax:
      return CFunctionCall('APIntOps::umax', *(arg.toAPInt() for arg in self.args))

    if self.op == self.width:
      return CFunctionCall('APInt',
        self.toCType().arr('getPrimitiveSizeInBits', []),
        self.args[0].toCType().arr('getPrimitiveSizeInBits', []))

    raise AliveError(self.opnames[self.op] + ' not implemented')

  def toAPIntOrLit(self):
    if self.op == self.width:
      return self.args[0].toCType().arr('getPrimitiveSizeInBits',[])

    return self.toAPInt()

  def setRepresentative(self, manager):
    self._manager = manager
    manager.add_label(self.getLabel(), self.type, anon=True)

    for arg in self.args:
      arg.setRepresentative(manager)

    if self.op == self.abs:
      manager.unify(self.getLabel(), self.args[0].getLabel())

    elif self.op == self.lshr or self.op == self.umax:
      manager.unify(self.getLabel(), self.args[0].getLabel(), self.args[1].getLabel())

    elif self.op == self.trunc or self.op == self.width:
      pass

    else:
      raise AliveError('setRepresentative not implemented for' + self.opnames[self.op])
      
