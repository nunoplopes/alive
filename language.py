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

from z3 import *
import math

class Type:
  def __repr__(self):
    return ''


################################
class IntType(Type):
  def __init__(self, size = None):
    if size == None:
      self.defined = False
      return
    self.size = size
    self.defined = True
    assert isinstance(self.size, int)

  def __repr__(self):
    if self.defined:
      return 'i' + str(self.size)
    return ''

  def getIntSize(self):
    return self.size

  def fixupSize(self, size):
    assert self.defined == False or self.size == size
    self.size = size

  def getSMTName(self, instr):
    return Int('t' + instr.getName())

  def getConstraints(self, instr, vars):
    v = self.getSMTName(instr)
    vars += [v]
    if self.defined:
      return v == self.getIntSize()
    return BoolVal(True)


################################
class Instr:
  def __repr__(self):
    return self.toString()

  def getName(self):
    return self.name

  def setName(self, name):
    self.name = name

  def toString(self):
    raise Exception('toString not implemented')

  def getTypeSMTName(self):
    return self.type.getSMTName(self)

  def getTypeConstraints(self, vars):
    return self.type.getConstraints(self, vars)

  def fixupTypes(self, types):
    self.type.fixupSize(types.evaluate(self.getTypeSMTName()).as_long())


################################
class Input(Instr):
  def __init__(self, name, type):
    self.setName(name)
    self.type = type
    assert isinstance(self.type, Type)

  def toString(self):
    return self.getName()

  def toSMT(self, defined):
    return BitVec(self.name, self.type.getIntSize())


################################
class Constant(Instr):
  last_id = 0

  def __init__(self, val, type):
    self.val = val
    self.type = type
    self.setName(str(val))
    self.SMTTypeVar = Int(self.mkSMTTypeName())
    assert isinstance(self.type, Type)

  def toString(self):
    return str(self.val)

  def toSMT(self, defined):
    return BitVecVal(self.val, self.type.getIntSize())

  def mkSMTTypeName(self):
    id = Constant.last_id
    Constant.last_id += 1
    return str('t%d_%d' % (self.val, id))

  def getTypeSMTName(self):
    return self.SMTTypeVar

  def getTypeConstraints(self, vars):
    v = self.getTypeSMTName()
    vars += [v]
    if self.type.defined:
      return v == self.type.getIntSize()
    if self.val != 0:
      bits = int(math.ceil(math.log(abs(self.val), 2)))
      return v >= bits
    return BoolVal(True)


################################
class BinOp(Instr):
  Add, Sub, Mul, UDiv, SDiv, URem, SRem, Shl, AShr, LShr, And, Or, Xor,\
  Last = range(14)

  opnames = {
    Add:  'add',
    Sub:  'sub',
    Mul:  'mul',
    UDiv: 'udiv',
    SDiv: 'sdiv',
    URem: 'urem',
    SRem: 'srem',
    Shl:  'shl',
    AShr: 'ashr',
    LShr: 'lshr',
    And:  'and',
    Or:   'or',
    Xor:  'xor',
  }
  opids = {v:k for k, v in opnames.items()}


  def __init__(self, op, type, v1, v2, flags = []):
    self.op = op
    self.type = type
    self.v1 = v1
    self.v2 = v2
    self.flags = flags
    self._check_op_flags()
    assert isinstance(self.type, Type)
    assert isinstance(self.v1, Instr)
    assert isinstance(self.v2, Instr)
    assert self.op >= 0 and self.op < self.Last

  def getOpName(self):
    return self.opnames[self.op]

  @staticmethod
  def getOpId(name):
    try:
      return BinOp.opids[name]
    except:
      print 'Unknown binary instruction: ' + name
      exit(-1)

  def toString(self):
    t = str(self.type)
    if len(t) > 0:
      t = ' ' + t
    flags = ' '.join(self.flags)
    if len(flags) > 0:
      flags = ' ' + flags
    return '%s%s%s %s, %s' % (self.getOpName(), flags, t,
                              self.v1.getName(),
                              self.v2.getName())

  def _check_op_flags(self):
    allowed_flags = {
      self.Add:  ['nsw', 'nuw'],
      self.Sub:  ['nsw', 'nuw'],
      self.Mul:  ['nsw', 'nuw'],
      self.UDiv: ['exact'],
      self.SDiv: ['exact'],
      self.URem: [],
      self.SRem: [],
      self.Shl:  ['nsw', 'nuw'],
      self.AShr: ['exact'],
      self.LShr: ['exact'],
      self.And:  [],
      self.Or:   [],
      self.Xor:  [],
    }[self.op]

    for f in self.flags:
      if f not in allowed_flags:
        print 'Flag \'%s\' not support by instruction \'%s\'' %\
              (f, self.getOpName())
        exit(-1)

  def _genSMTDefConds(self, v1, v2, defined):
    bits = self.type.getIntSize()

    def_conds = {
      self.Add: {'nsw': lambda a,b: SignExt(1,a)+SignExt(1,b) == SignExt(1,a+b),
                 'nuw': lambda a,b: ZeroExt(1,a)+ZeroExt(1,b) == ZeroExt(1,a+b),
                },
      self.Sub: {'nsw': lambda a,b: SignExt(1,a)-SignExt(1,b) == SignExt(1,a-b),
                 'nuw': lambda a,b: ZeroExt(1,a)-ZeroExt(1,b) == ZeroExt(1,a-b),
                },
      self.Mul: {'nsw': lambda a,b: SignExt(bits, a) * SignExt(bits, b) ==
                                    SignExt(bits, a * b),
                 'nuw': lambda a,b: ZeroExt(bits, a) * ZeroExt(bits, b) ==
                                    ZeroExt(bits, a * b),
                },
      self.UDiv:{'exact': lambda a,b: UDiv(a, b) * b == a,
                },
      self.SDiv:{'exact': lambda a,b: (a / b) * b == a,
                },
      self.URem:{},
      self.SRem:{},
      self.Shl: {'nsw': lambda a,b: (a << b) >> b == a,
                 'nuw': lambda a,b: LShR(a << b, b) == a,
                },
      self.AShr:{'exact': lambda a,b: (a >> b) << b == a,
                },
      self.LShr:{'exact': lambda a,b: LShR(a, b) << b == a,
                },
      self.And: {},
      self.Or:  {},
      self.Xor: {},
    }[self.op]

    for f in self.flags:
      defined += [def_conds[f](v1, v2)]

    # additional constraints of definedness of the instruction
    defined += {
      self.Add:  lambda a,b: [],
      self.Sub:  lambda a,b: [],
      self.Mul:  lambda a,b: [],
      self.UDiv: lambda a,b: [b != 0],
      self.SDiv: lambda a,b: [And(b != 0, Or(a != (1 << (bits-1)), b != -1))],
      self.URem: lambda a,b: [b != 0],
      self.SRem: lambda a,b: [And(b != 0, Or(a != (1 << (bits-1)), b != -1))],
      self.Shl:  lambda a,b: [ULT(b, bits)],
      self.AShr: lambda a,b: [ULT(b, bits)],
      self.LShr: lambda a,b: [ULT(b, bits)],
      self.And:  lambda a,b: [],
      self.Or:   lambda a,b: [],
      self.Xor:  lambda a,b: [],
      }[self.op](v1,v2)
    return

  def toSMT(self, defined):
    v1 = self.v1.toSMT(defined)
    v2 = self.v2.toSMT(defined)
    self._genSMTDefConds(v1, v2, defined)
    return {
      self.Add:  lambda a,b: a + b,
      self.Sub:  lambda a,b: a - b,
      self.Mul:  lambda a,b: a * b,
      self.UDiv: lambda a,b: UDiv(a, b),
      self.SDiv: lambda a,b: a / b,
      self.URem: lambda a,b: URem(a, b),
      self.SRem: lambda a,b: SRem(a, b),
      self.Shl:  lambda a,b: a << b,
      self.AShr: lambda a,b: a >> b,
      self.LShr: lambda a,b: LShR(a, b),
      self.And:  lambda a,b: a & b,
      self.Or:   lambda a,b: a | b,
      self.Xor:  lambda a,b: a ^ b,
    }[self.op](v1, v2)

  def getTypeConstraints(self, vars):
    my_type = self.getTypeSMTName()
    return And(self.type.getConstraints(self, vars),
               my_type == self.v1.getTypeSMTName(),
               my_type == self.v2.getTypeSMTName())


################################
class ConversionOp(Instr):
  Trunc, ZExt, SExt, Last = range(4)

  opnames = {
    Trunc: 'trunc',
    ZExt:  'zext',
    SExt:  'sext',
  }
  opids = {v:k for k, v in opnames.items()}

  def __init__(self, op, stype, v, ttype):
    self.op = op
    self.stype = stype
    self.v = v
    self.type = ttype
    assert isinstance(self.stype, Type)
    assert isinstance(self.type, Type)
    assert isinstance(self.v, Instr)
    assert self.op >= 0 and self.op < self.Last

  def getOpName(self):
    return self.opnames[self.op]

  @staticmethod
  def getOpId(name):
    try:
      return ConversionOp.opids[name]
    except:
      print 'Unknown conversion instruction: ' + name
      exit(-1)

  def toString(self):
    st = str(self.stype)
    if len(st) > 0:
      st = ' ' + st
    tt = str(self.type)
    if len(tt) > 0:
      tt = ' to ' + tt
    return '%s%s %s%s' % (self.getOpName(), st, self.v.getName(), tt)

  def toSMT(self, defined):
    v = self.v.toSMT(defined)
    delta_bits = self.type.getIntSize() - self.stype.getIntSize()
    return {
      self.Trunc: lambda v: Extract(self.type.getIntSize()-1, 0, v),
      self.ZExt:  lambda v: ZeroExt(delta_bits, v),
      self.SExt:  lambda v: SignExt(delta_bits, v),
    }[self.op](v)

  def getTypeConstraints(self, vars):
    my_type = self.getTypeSMTName()
    srctype = self.v.getTypeSMTName()
    cnstr = {
      self.Trunc: lambda src,tgt: src > tgt,
      self.ZExt:  lambda src,tgt: src < tgt,
      self.SExt:  lambda src,tgt: src < tgt,
    } [self.op](srctype, my_type)

    c = [self.type.getConstraints(self, vars), cnstr]
    if self.stype.defined:
      c += [srctype == self.stype.getIntSize()]
    return And(c)

  def fixupTypes(self, types):
    self.type.fixupSize(types.evaluate(self.getTypeSMTName()).as_long())
    self.stype.fixupSize(types.evaluate(self.v.getTypeSMTName()).as_long())


################################
class Icmp(Instr):
  EQ, NE, UGT, UGE, ULT, ULE, SGT, SGE, SLT, SLE, Var, Last = range(12)

  opnames = {
    EQ:  'eq',
    NE:  'ne',
    UGT: 'ugt',
    UGE: 'uge',
    ULT: 'ult',
    ULE: 'ule',
    SGT: 'sgt',
    SGE: 'sge',
    SLT: 'slt',
    SLE: 'sle',
  }
  opids = {v:k for k, v in opnames.items()}


  def __init__(self, op, type, v1, v2):
    self.op = self.getOpId(op)
    if self.op == self.Var:
      self.opname = op
    self.type = type
    self.v1 = v1
    self.v2 = v2
    assert isinstance(self.type, Type)
    assert isinstance(self.v1, Instr)
    assert isinstance(self.v2, Instr)

  @staticmethod
  def getOpId(name):
    return Icmp.opids.get(name, Icmp.Var)

  def toString(self):
    op = self.opname if self.op == Icmp.Var else Icmp.opnames[self.op]
    if len(op) > 0:
      op = ' ' + op
    t = str(self.type)
    if len(t) > 0:
      t = ' ' + t
    return 'icmp%s%s %s, %s' % (op, t, self.v1.getName(), self.v2.getName())

  @staticmethod
  def toBV(b):
    return If(b, BitVecVal(1, 1), BitVecVal(0, 1))

  def opToSMT(self, op, a, b):
    return {
      self.EQ:  lambda a,b: Icmp.toBV(a == b),
      self.NE:  lambda a,b: Icmp.toBV(a != b),
      self.UGT: lambda a,b: Icmp.toBV(UGT(a, b)),
      self.UGE: lambda a,b: Icmp.toBV(UGE(a, b)),
      self.ULT: lambda a,b: Icmp.toBV(ULT(a, b)),
      self.ULE: lambda a,b: Icmp.toBV(ULE(a, b)),
      self.SGT: lambda a,b: Icmp.toBV(a > b),
      self.SGE: lambda a,b: Icmp.toBV(a >= b),
      self.SLT: lambda a,b: Icmp.toBV(a < b),
      self.SLE: lambda a,b: Icmp.toBV(a <= b),
    }[op](a, b)

  def recurseSMT(self, ops, a, b, i):
    if len(ops) == 1:
      return self.opToSMT(ops[0], a, b)
    var = BitVec('icmp_' + self.opname, 4)
    assert 1 << 4 > self.Var
    return If(var == i,
              self.opToSMT(ops[0], a, b),
              self.recurseSMT(ops[1:], a, b, i+1))

  def toSMT(self, defined):
    # Generate all possible comparisons if icmp is generic. Set of comparisons
    # can be restricted in the precondition.
    ops = [self.op] if self.op != self.Var else range(self.Var)
    return self.recurseSMT(ops, self.v1.toSMT(defined),
                           self.v2.toSMT(defined), 0)

  def getTypeConstraints(self, vars):
    c = [self.v1.getTypeSMTName() == self.v2.getTypeSMTName(),
         self.getTypeSMTName() == 1]
    if self.type.defined:
      c += [self.v1.getTypeSMTName() == self.type.getIntSize()]
    return And(c)

  def fixupTypes(self, types):
    self.type.fixupSize(types.evaluate(self.v1.getTypeSMTName()).as_long())


################################
def print_prog(p):
  for i in p.itervalues():
    if isinstance(i, Input) or isinstance(i, Constant):
      continue
    print '%s = %s' % (i.getName(), i)


def getTypeConstraints(p, vars):
  return [v.getTypeConstraints(vars) for v in p.itervalues()]


def fixupTypes(p, types):
  for v in p.itervalues():
    v.fixupTypes(types)
