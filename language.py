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

import math, collections, copy
from common import *


gbl_unique_id = 0
def mk_unique_id():
  global gbl_unique_id
  id = str(gbl_unique_id)
  gbl_unique_id += 1
  return id


################################
class State:
  def __init__(self):
    self.vars = collections.OrderedDict()
    self.ptrs = []

  def add(self, v, smt, defined, qvars):
    if v.getUniqueName() == '':
      return
    self.vars[v.getUniqueName()] = (smt, defined, qvars)

  def addAlloca(self, ptr, size, mem):
    self.ptrs += [(ptr, size, mem)]

  def getAllocaConstraints(self):
    ptrs = [ptr for (ptr, size, mem) in self.ptrs]
    return mk_distinct(ptrs)

  def eval(self, v, defined, qvars):
    (smt, d, q) = self.vars[v.getUniqueName()]
    defined += d
    qvars += q
    return smt

  def iteritems(self):
    for k,v in self.vars.iteritems():
      if k[0] != '%':
        continue
      yield k,v

  def has_key(self, k):
    return self.vars.has_key(k)

  def __getitem__(self, k):
    return self.vars[k]


################################
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

  def setName(self, name):
    self.smtvar = Int('t' + name)

  def __repr__(self):
    if self.defined:
      return 'i' + str(self.size)
    return ''

  def getIntSize(self):
    return self.size

  def getSize(self):
    return self.size

  def fixup(self, types):
    size = types.evaluate(self.smtvar).as_long()
    assert self.defined == False or self.size == size
    self.size = size

  def __eq__(self, other):
    if isinstance(other, IntType):
      return self.smtvar == other.smtvar
    if isinstance(other, int):
      return self.smtvar == other
    assert False

  def __lt__(self, other):
    if isinstance(other, IntType):
      return self.smtvar < other.smtvar
    if isinstance(other, int):
      return self.smtvar < other
    assert False

  def __gt__(self, other):
    if isinstance(other, IntType):
      return self.smtvar > other.smtvar
    if isinstance(other, int):
      return self.smtvar > other
    assert False

  def __ge__(self, other):
    if isinstance(other, IntType):
      return self.smtvar >= other.smtvar
    if isinstance(other, int):
      return self.smtvar >= other
    assert False

  def getConstraints(self, vars):
    vars += [self.smtvar]
    if self.defined:
      return self.smtvar == self.getIntSize()
    return BoolVal(True)


################################
class PtrType(Type):
  def __init__(self, type):
    self.type = type
    assert isinstance(self.type, Type)

  def __repr__(self):
    return str(self.type) + '*'

  def setName(self, name):
    self.type.setName('*'+name)

  def getSize(self):
    return self.size

  def getPointeeSize(self):
    return self.type.getSize()

  def __eq__(self, other):
    if isinstance(other, PtrType):
      return self.type == other.type
    assert False

  def fixup(self, types):
    self.size = types.evaluate(Int('ptrsize')).as_long()
    self.type.fixup(types)

  def getConstraints(self, vars):
    # Pointers are assumed to be either 32 or 64 bits
    v = Int('ptrsize')
    return And(Or(v == 32, v == 64),
               self.type.getConstraints(vars))


################################
class Instr:
  def __repr__(self):
    return self.toString()

  def getName(self):
    return self.name

  def getUniqueName(self):
    return self.name

  def setName(self, name):
    self.name = name
    self.type = copy.deepcopy(self.type)
    self.type.setName(name)
    for attr in dir(self):
      a = getattr(self, attr)
      if isinstance(a, TypeFixedValue):
        a.setName(name, attr)
        setattr(self, attr, a)
      elif isinstance(a, Type) and attr != 'type':
        a = copy.deepcopy(a)
        a.setName('%s_%s_%s' % (name, attr, mk_unique_id()))
        setattr(self, attr, a)

  def getTypeConstraints(self, vars):
    c = []
    for attr in dir(self):
      a = getattr(self, attr)
      if isinstance(a, Type):
        c += [a.getConstraints(vars)]
      elif isinstance(a, Instr):
        c += [a.getTypeConstraints(vars)]
    return mk_and(c)

  def fixupTypes(self, types):
    for attr in dir(self):
      a = getattr(self, attr)
      if isinstance(a, Instr):
        a.fixupTypes(types)
      elif isinstance(a, Type):
        a.fixup(types)


################################
class TypeFixedValue(Instr):
  def __init__(self, v, min, max):
    self.v = v
    self.min = min
    self.max = max
    assert isinstance(self.v, Instr)

  def setName(self, name, attr):
    self.name = self.v.getName()
    self.smtvar = Int('val_%s_%s' % (name, attr))

  def getValue(self):
    return self.val

  def getType(self):
    return self.v.type

  def toString(self):
    return self.v.toString()

  def toSMT(self, defined, state, qvars):
    defined += [state.eval(self.v, defined, qvars) == self.val]
    return self.val

  def getTypeConstraints(self, vars):
    if isinstance(self.v, Constant) and not isinstance(self.v, UndefVal):
      return self.smtvar == self.v.val
    return And(self.smtvar >= self.min, self.smtvar <= self.max)

  def fixupTypes(self, types):
    self.v.fixupTypes(types)
    self.val = types.evaluate(self.smtvar).as_long()


################################
class Input(Instr):
  def __init__(self, name, type):
    self.type = type
    self.setName(name)
    assert isinstance(self.type, Type)

  def toString(self):
    return self.getName()

  def toSMT(self, defined, state, qvars):
    return BitVec(self.name, self.type.getIntSize())


################################
class CopyOperand(Instr):
  def __init__(self, v, type):
    self.v = v
    self.type = type
    assert isinstance(self.v, Instr)
    assert isinstance(self.type, Type)

  def toString(self):
    return self.v.toString()

  def toSMT(self, defined, state, qvars):
    return state.eval(self.v, defined, qvars)

  def getTypeConstraints(self, vars):
    return And(self.type.getConstraints(vars),
               self.type == self.v.type)


################################
class Constant(Instr):
  def __init__(self, val, type):
    self.val = val
    self.type = type
    self.setName(str(val))
    self.id = mk_unique_id()
    self.type.setName(self.getUniqueName())
    assert isinstance(self.type, Type)

  def getUniqueName(self):
    return self.getName() + '_' + self.id

  def toString(self):
    if isinstance(self.type, PtrType) and self.val == 0:
      return 'null'
    return str(self.val)

  def toSMT(self, defined, state, qvars):
    return BitVecVal(self.val, self.type.getSize())

  def getTypeConstraints(self, vars):
    c = self.type.getConstraints(vars)
    if self.val != 0:
      if self.val > 0:
        bits = int(math.floor(math.log(self.val, 2)+1))
      else:
        bits = int(math.floor(math.log(abs(self.val)+1, 2)+1))
      return And(c, self.type >= bits)
    return c


################################
class UndefVal(Constant):
  def __init__(self, type):
    self.type = type
    self.setName('undef')
    self.id = mk_unique_id()
    self.type.setName(self.getUniqueName())
    assert isinstance(self.type, Type)

  def toString(self):
    return 'undef'

  def toSMT(self, defined, state, qvars):
    v = BitVec('undef' + self.id, self.type.getIntSize())
    qvars += [v]
    return v

  def getTypeConstraints(self, vars):
    # overload Constant's method
    return self.type.getConstraints(vars)


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

  def toSMT(self, defined, state, qvars):
    v1 = state.eval(self.v1, defined, qvars)
    v2 = state.eval(self.v2, defined, qvars)
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
    return And(self.type.getConstraints(vars),
               self.type == self.v1.type,
               self.type == self.v2.type)


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

  def toSMT(self, defined, state, qvars):
    delta_bits = self.type.getIntSize() - self.stype.getIntSize()
    return {
      self.Trunc: lambda v: Extract(self.type.getIntSize()-1, 0, v),
      self.ZExt:  lambda v: ZeroExt(delta_bits, v),
      self.SExt:  lambda v: SignExt(delta_bits, v),
    }[self.op](state.eval(self.v, defined, qvars))

  def getTypeConstraints(self, vars):
    cnstr = {
      self.Trunc: lambda src,tgt: src > tgt,
      self.ZExt:  lambda src,tgt: src < tgt,
      self.SExt:  lambda src,tgt: src < tgt,
    } [self.op](self.stype, self.type)

    return And(self.type.getConstraints(vars),
               self.stype.getConstraints(vars),
               self.stype == self.v.type,
               cnstr)


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
    self.type = IntType(1)
    self.stype = type
    self.v1 = v1
    self.v2 = v2
    assert isinstance(self.stype, Type)
    assert isinstance(self.v1, Instr)
    assert isinstance(self.v2, Instr)

  @staticmethod
  def getOpId(name):
    return Icmp.opids.get(name, Icmp.Var)

  def toString(self):
    op = self.opname if self.op == Icmp.Var else Icmp.opnames[self.op]
    if len(op) > 0:
      op = ' ' + op
    t = str(self.stype)
    if len(t) > 0:
      t = ' ' + t
    return 'icmp%s%s %s, %s' % (op, t, self.v1.getName(), self.v2.getName())

  def opToSMT(self, op, a, b):
    return {
      self.EQ:  lambda a,b: toBV(a == b),
      self.NE:  lambda a,b: toBV(a != b),
      self.UGT: lambda a,b: toBV(UGT(a, b)),
      self.UGE: lambda a,b: toBV(UGE(a, b)),
      self.ULT: lambda a,b: toBV(ULT(a, b)),
      self.ULE: lambda a,b: toBV(ULE(a, b)),
      self.SGT: lambda a,b: toBV(a > b),
      self.SGE: lambda a,b: toBV(a >= b),
      self.SLT: lambda a,b: toBV(a < b),
      self.SLE: lambda a,b: toBV(a <= b),
    }[op](a, b)

  def recurseSMT(self, ops, a, b, i):
    if len(ops) == 1:
      return self.opToSMT(ops[0], a, b)
    var = BitVec('icmp_' + self.opname, 4)
    assert 1 << 4 > self.Var
    return If(var == i,
              self.opToSMT(ops[0], a, b),
              self.recurseSMT(ops[1:], a, b, i+1))

  def toSMT(self, defined, state, qvars):
    # Generate all possible comparisons if icmp is generic. Set of comparisons
    # can be restricted in the precondition.
    ops = [self.op] if self.op != self.Var else range(self.Var)
    return self.recurseSMT(ops, state.eval(self.v1, defined, qvars),
                           state.eval(self.v2, defined, qvars), 0)

  def getTypeConstraints(self, vars):
    return And(self.type.getConstraints(vars),
               self.stype.getConstraints(vars),
               self.stype == self.v1.type,
               self.stype == self.v2.type)


################################
class Select(Instr):
  def __init__(self, type, c, v1, v2):
    self.type = type
    self.c = c
    self.v1 = v1
    self.v2 = v2
    assert isinstance(self.type, Type)
    assert isinstance(self.c, Instr)
    assert isinstance(self.v1, Instr)
    assert isinstance(self.v2, Instr)

  def toString(self):
    t = str(self.type)
    if len(t) > 0:
      t = t + ' '
    return 'select i1 %s, %s%s, %s%s' % (self.c, t, self.v1, t, self.v2)

  def toSMT(self, defined, state, qvars):
    return If(state.eval(self.c, defined, qvars) == 1,
              state.eval(self.v1, defined, qvars),
              state.eval(self.v2, defined, qvars))

  def getTypeConstraints(self, vars):
    return And(self.type.getConstraints(vars),
               self.type == self.v1.type,
               self.type == self.v2.type,
               self.c.type == 1)


################################
class Alloca(Instr):
  def __init__(self, type, elemsType, numElems, align):
    self.type = PtrType(type)
    self.elemsType = elemsType
    self.numElems = TypeFixedValue(numElems, 1, 16)
    self.align = align
    assert isinstance(self.elemsType, Type)
    assert isinstance(self.align, int)

  def toString(self):
    elems = self.numElems.getName()
    if elems == '1':
      elems = ''
    else:
      t = str(self.elemsType)
      if len(t) > 0:
        t += ' '
      elems =  ', ' + t + elems
    align = ', align %d' % self.align if self.align != 0 else ''
    return 'alloca %s%s%s' % (str(self.type.type), elems, align)

  def toSMT(self, defined, state, qvars):
    ## TODO: size in bits vs bytes
    ptr = BitVec('ptralloca' + self.getName(), self.type.size)
    size = self.numElems.getValue() * self.type.getPointeeSize()
    defined += [ULT(ptr, ptr + size), ptr != 0]
    state.addAlloca(ptr, size, BitVec('alloca' + self.getName(), size))
    return ptr


  def getTypeConstraints(self, vars):
    return And(self.type.getConstraints(vars),
               self.elemsType.getConstraints(vars),
               self.numElems.getTypeConstraints(vars),
               self.numElems.getType() == self.elemsType)


################################
class Load(Instr):
  def __init__(self, stype, v, align):
    self.stype = stype
    self.type = stype.type
    self.v = v
    self.align = align
    assert isinstance(self.stype, PtrType)
    assert isinstance(self.v, Instr)
    assert isinstance(self.align, int)

  def toString(self):
    align = ', align %d' % self.align if self.align != 0 else ''
    return 'load %s %s%s' % (str(self.stype), self.v.getName(), align)

  def _recPtrLoad(self, l, v):
    (ptr, size, mem) = l[0]
    if size > self.type.getSize():
      offset = v - ptr
      mem = mem << truncateOrZExt(offset, mem)
      mem = Extract(size - 1, size - self.type.getSize(), mem)
    elif size < self.type.getSize():
      # undef behavior
      #TODO..
      mem = BitVecVal(0, size)

    if len(l) == 1:
      return mem
    return If(And(UGE(v, ptr), ULT(v, ptr+size)),
              mem,
              _recPtrLoad(l[1:]))

  def toSMT(self, defined, state, qvars):
    v = state.eval(self.v, defined, qvars)

    # Reading from a random location is undefined
    d = [And(UGE(v, ptr), ULE(v + self.type.getSize(), ptr + size))\
      for (ptr, size, mem) in state.ptrs]
    defined += [mk_or(d), v != 0]

    return self._recPtrLoad(state.ptrs, v)

  def getTypeConstraints(self, vars):
    return And(self.type.getConstraints(vars),
               self.v.type == self.stype)


################################
class Store(Instr):
  def __init__(self, stype, src, type, dst, align):
    self.stype = stype
    self.src = src
    self.type = type
    self.dst = dst
    self.align = align
    self.setName('store')
    self.id = mk_unique_id()
    self.type.setName(self.getUniqueName())
    assert isinstance(self.stype, Type)
    assert isinstance(self.src, Instr)
    assert isinstance(self.type, PtrType)
    assert isinstance(self.dst, Instr)
    assert isinstance(self.align, int)

  def getUniqueName(self):
    return self.getName() + '_' + self.id

  def toString(self):
    t = str(self.stype)
    if len(t) > 0:
      t = t + ' '
    align = ', align %d' % self.align if self.align != 0 else ''
    return 'store %s%s, %s %s%s' % (t, self.src.getName(), str(self.type),
                                    self.dst.getName(), align)

  def _mkMem(self, src, tgt, ptr, size, mem):
    write_size = self.stype.getSize()
    if write_size == size:
      return src
    offset = tgt - ptr
    new = LShR(truncateOrPad(src, mem), truncateOrZExt(offset, mem))

    # mask out bits that will be written
    mask = BitVecVal((1 << size) - 1, size)
    m1 = mask << truncateOrZExt(size - offset, mem)
    m2 = LShR(mask, truncateOrZExt(write_size + offset, mem))
    old = mem & (m1 | m2)
    return new | old

  def toSMT(self, defined, state, qvars):
    src = state.eval(self.src, defined, qvars)
    tgt = state.eval(self.dst, defined, qvars)

    # Writing to a random location is undefined
    d = [And(UGE(tgt, ptr), ULT(tgt, ptr+size)) \
           for (ptr, size, mem) in state.ptrs]
    defined += [mk_or(d), tgt != 0]

    newmem = []
    for (ptr, size, mem) in state.ptrs:
      mem = If(And(UGE(tgt, ptr), ULE(tgt + self.stype.getSize(), ptr + size)),
               self._mkMem(src, tgt, ptr, size, mem),
               mem)
      newmem += [(ptr, size, mem)]
    state.ptrs = newmem
    return None

  def getTypeConstraints(self, vars):
    return And(self.stype.getConstraints(vars),
               self.type.getConstraints(vars),
               self.src.type == self.stype,
               self.dst.type == self.type)


################################
def print_prog(p):
  for k,v in p.iteritems():
    if isinstance(v, Input) or isinstance(v, Constant):
      continue
    if isinstance(v, Store):
      print v
    else:
      print '%s = %s' % (k, v)


def getTypeConstraints(p, vars):
  return [v.getTypeConstraints(vars) for v in p.itervalues()]


def fixupTypes(p, types):
  for v in p.itervalues():
    v.fixupTypes(types)


def toSMT(prog):
  state = State()
  for k,v in prog.iteritems():
    defined = []
    qvars = []
    smt = v.toSMT(defined, state, qvars)
    state.add(v, smt, defined, qvars)
  return state
