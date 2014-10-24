# Copyright 2014 The Alive authors.
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

import collections
from constants import *


def getAllocSize(type):
  # round to nearest byte boundary
  return int((type.getSize() + 7) / 8) * 8


def alignSize(size, align):
  if align == 0:
    return size
  assert align & (align-1) == 0
  return (size + (align-1)) & ~(align-1)


def getPtrAlignCnstr(ptr, align):
  if align == 0:
    return BoolVal(True)
  assert align & (align-1) == 0
  return ptr & (align-1) == 0


################################
class State:
  def __init__(self):
    self.vars = collections.OrderedDict()
    self.defined = [] # definedness so far in the BB
    self.ptrs = []
    self.bb_pres = {}

  def add(self, v, smt, defined, poison, qvars):
    if v.getUniqueName() == '':
      return
    self.defined = self.defined + defined
    self.vars[v.getUniqueName()] = (smt, self.defined, poison, qvars)
    if isinstance(v, TerminatorInst):
      for (bb,cond) in v.getSuccessors(self):
        bb = bb[1:]
        if bb not in self.bb_pres:
          self.bb_pres[bb] = []
        self.bb_pres[bb] += [cond]

  def addAlloca(self, ptr, mem, info):
    self.ptrs += [(ptr, mem, [mem], info)]

  def addInputMem(self, ptr, mem, info):
    self.ptrs += [(ptr, mem, [], info)]

  def newBB(self, name):
    if name in self.bb_pres:
      self.defined = [mk_or(self.bb_pres[name])]
    else:
      self.defined = []
    self.current_bb = name

  def getAllocaConstraints(self):
    ptrs = [ptr for (ptr, mem, qvars, info) in self.ptrs]
    return mk_distinct(ptrs)

  def eval(self, v, poison, qvars):
    (smt, d, p, q) = self.vars[v.getUniqueName()]
    poison += p
    qvars += q
    return smt

  def iteritems(self):
    for k,v in self.vars.iteritems():
      if k[0] != '%' and k[0] != 'C' and not k.startswith('ret_'):
        continue
      yield k,v

  def has_key(self, k):
    return self.vars.has_key(k)

  def __getitem__(self, k):
    return self.vars[k]


################################
class Instr(Value):
  pass


################################
class CopyOperand(Instr):
  def __init__(self, v, type):
    self.v = v
    self.type = type
    assert isinstance(self.v, Value)
    assert isinstance(self.type, Type)

  def __repr__(self):
    t = str(self.type)
    if len(t) > 0:
      t += ' '
    return t + self.v.getName()

  def toSMT(self, poison, state, qvars):
    return [], state.eval(self.v, poison, qvars)

  def getTypeConstraints(self):
    return And(self.type == self.v.type,
               self.type.getTypeConstraints())


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
    assert isinstance(type, Type)
    assert isinstance(v1, Value)
    assert isinstance(v2, Value)
    assert 0 <= op < self.Last
    self.op = op
    self.type = type
    self.v1 = v1
    self.v2 = v2
    self.flags = flags
    self._check_op_flags()

  def getOpName(self):
    return self.opnames[self.op]

  @staticmethod
  def getOpId(name):
    try:
      return BinOp.opids[name]
    except:
      raise ParseError('Unknown binary instruction')

  def __repr__(self):
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
        raise ParseError('Flag not supported by ' + self.getOpName(), f)

  def _genSMTDefConds(self, v1, v2, poison):
    bits = self.type.getSize()

    poison_conds = {
      self.Add: {'nsw': lambda a,b: SignExt(1,a)+SignExt(1,b) == SignExt(1,a+b),
                 'nuw': lambda a,b: ZeroExt(1,a)+ZeroExt(1,b) == ZeroExt(1,a+b),
                },
      self.Sub: {'nsw': lambda a,b: SignExt(1,a)-SignExt(1,b) == SignExt(1,a-b),
                 'nuw': lambda a,b: ZeroExt(1,a)-ZeroExt(1,b) == ZeroExt(1,a-b),
                },
      self.Mul: {'nsw': lambda a,b: no_overflow_smul(a, b),
                 'nuw': lambda a,b: no_overflow_umul(a, b),
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

    if do_infer_flags():
      for flag,fn in poison_conds.iteritems():
        bit = get_flag_var(flag, self.getName())
        poison += [Implies(bit == 1, fn(v1, v2))]
    else:
      for f in self.flags:
        poison += [poison_conds[f](v1, v2)]

    # definedness of the instruction
    return {
      self.Add:  lambda a,b: [],
      self.Sub:  lambda a,b: [],
      self.Mul:  lambda a,b: [],
      self.UDiv: lambda a,b: [b != 0],
      self.SDiv: lambda a,b: [b != 0, Or(a != (1 << (bits-1)), b != -1)],
      self.URem: lambda a,b: [b != 0],
      self.SRem: lambda a,b: [b != 0, Or(a != (1 << (bits-1)), b != -1)],
      self.Shl:  lambda a,b: [ULT(b, bits)],
      self.AShr: lambda a,b: [ULT(b, bits)],
      self.LShr: lambda a,b: [ULT(b, bits)],
      self.And:  lambda a,b: [],
      self.Or:   lambda a,b: [],
      self.Xor:  lambda a,b: [],
      }[self.op](v1,v2)

  def toSMT(self, poison, state, qvars):
    v1 = state.eval(self.v1, poison, qvars)
    v2 = state.eval(self.v2, poison, qvars)
    defined = self._genSMTDefConds(v1, v2, poison)
    return defined, {
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

  def getTypeConstraints(self):
    return And(self.type == self.v1.type,
               self.type == self.v2.type,
               self.type.getTypeConstraints())
  
  def getPatternMatch(self, context, name = None):
    if name == None: name = self.getCName()
    
    matcher = {
      self.Add:  'm_Add',
      self.Sub:  'm_Sub',
      self.Mul:  'm_Mul',
      self.UDiv: 'm_UDiv',
      self.SDiv: 'm_SDiv',
      self.URem: 'm_URem',
      self.SRem: 'm_SRem',
      self.Shl:  'm_Shl',
      self.AShr: 'm_AShr',
      self.LShr: 'm_LShr',
      self.And:  'm_And',
      self.Or:   'm_Or',
      self.Xor:  'm_Xor',
    }[self.op]
    v1 = context.ref(self.v1)
    v2 = context.ref(self.v2)
    
    return 'match({0}, {1}({2},{3}))'.format(name, matcher, v1, v2)


################################
class ConversionOp(Instr):
  Trunc, ZExt, SExt, ZExtOrTrunc, Ptr2Int, Int2Ptr, Bitcast, Last = range(8)

  opnames = {
    Trunc:       'trunc',
    ZExt:        'zext',
    SExt:        'sext',
    ZExtOrTrunc: 'ZExtOrTrunc',
    Ptr2Int:     'ptrtoint',
    Int2Ptr:     'inttoptr',
    Bitcast:     'bitcast',
  }
  opids = {v:k for k, v in opnames.items()}

  def __init__(self, op, stype, v, type):
    assert isinstance(stype, Type)
    assert isinstance(type, Type)
    assert isinstance(v, Value)
    assert 0 <= op < self.Last
    self.op = op
    self.stype = stype
    self.v = v
    self.type = type

  def getOpName(self):
    return self.opnames[self.op]

  @staticmethod
  def getOpId(name):
    try:
      return ConversionOp.opids[name]
    except:
      raise ParseError('Unknown conversion instruction')

  @staticmethod
  def enforceIntSrc(op):
    return op == ConversionOp.Trunc or\
           op == ConversionOp.ZExt or\
           op == ConversionOp.SExt or\
           op == ConversionOp.ZExtOrTrunc or\
           op == ConversionOp.Int2Ptr

  @staticmethod
  def enforcePtrSrc(op):
    return op == ConversionOp.Ptr2Int

  @staticmethod
  def enforceIntTgt(op):
    return op == ConversionOp.Trunc or\
           op == ConversionOp.ZExt or\
           op == ConversionOp.SExt or\
           op == ConversionOp.ZExtOrTrunc or\
           op == ConversionOp.Ptr2Int

  @staticmethod
  def enforcePtrTgt(op):
    return op == ConversionOp.Int2Ptr

  def __repr__(self):
    st = str(self.stype)
    if len(st) > 0:
      st = ' ' + st
    tt = str(self.type)
    if len(tt) > 0:
      tt = ' to ' + tt
    return '%s%s %s%s' % (self.getOpName(), st, self.v.getName(), tt)

  def toSMT(self, poison, state, qvars):
    return [], {
      self.Trunc:       lambda v: Extract(self.type.getSize()-1, 0, v),
      self.ZExt:        lambda v: ZeroExt(self.type.getSize() -
                                         self.stype.getSize(), v),
      self.SExt:        lambda v: SignExt(self.type.getSize() -
                                          self.stype.getSize(), v),
      self.ZExtOrTrunc: lambda v: truncateOrZExt(v, self.type.getSize()),
      self.Ptr2Int:     lambda v: truncateOrZExt(v, self.type.getSize()),
      self.Int2Ptr:     lambda v: truncateOrZExt(v, self.type.getSize()),
      self.Bitcast:     lambda v: v,
    }[self.op](state.eval(self.v, poison, qvars))

  def getTypeConstraints(self):
    cnstr = {
      self.Trunc:       lambda src,tgt: src > tgt,
      self.ZExt:        lambda src,tgt: src < tgt,
      self.SExt:        lambda src,tgt: src < tgt,
      self.ZExtOrTrunc: lambda src,tgt: BoolVal(True),
      self.Ptr2Int:     lambda src,tgt: BoolVal(True),
      self.Int2Ptr:     lambda src,tgt: BoolVal(True),
      self.Bitcast:     lambda src,tgt: src.getSize() == tgt.getSize(),
    } [self.op](self.stype, self.type)

    return And(self.stype == self.v.type,
               self.type.getTypeConstraints(),
               self.stype.getTypeConstraints(),
               cnstr)

  def getPatternMatch(self, context, name = None):
    if name == None: name = self.getCName();
    
    if self.op == self.Int2Ptr:
      raise AliveError('inttoptr not supported?')
    
    matcher = {
      self.Trunc:   'm_Trunc',
      self.ZExt:    'm_ZExt',
      self.SExt:    'm_SExt',
      self.Ptr2Int: 'm_PtrToInt',
#       self.Int2Ptr: '   # no m_IntToPtr?
      self.Bitcast: 'm_BitCast',
    }[self.op]
    
    return 'match({0}, {1}({2}))'.format(name, matcher, context.ref(self.v))


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
    assert isinstance(type, Type)
    assert isinstance(v1, Value)
    assert isinstance(v2, Value)
    self.op = self.getOpId(op)
    if self.op == self.Var:
      self.opname = op
    self.type = IntType(1)
    self.stype = type.ensureIntPtrOrVector()
    self.v1 = v1
    self.v2 = v2

  @staticmethod
  def getOpId(name):
    return Icmp.opids.get(name, Icmp.Var)

  def __repr__(self):
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
    opname = self.opname if self.opname != '' else self.getName()
    var = BitVec('icmp_' + opname, 4)
    assert 1 << 4 > self.Var
    return If(var == i,
              self.opToSMT(ops[0], a, b),
              self.recurseSMT(ops[1:], a, b, i+1))

  def toSMT(self, poison, state, qvars):
    # Generate all possible comparisons if icmp is generic. Set of comparisons
    # can be restricted in the precondition.
    ops = [self.op] if self.op != self.Var else range(self.Var)
    return [], self.recurseSMT(ops, state.eval(self.v1, poison, qvars),
                               state.eval(self.v2, poison, qvars), 0)

  def getTypeConstraints(self):
    return And(self.stype == self.v1.type,
               self.stype == self.v2.type,
               self.type.getTypeConstraints(),
               self.stype.getTypeConstraints())

  def getPatternMatch(self, context, name = None):
    if name == None: name = self.getCName()
    
    if self.op == Icmp.Var:
      opname = 'P_' + self._mungeCName(self.opname)
      extra = ''
    else:
      opname = 'P_' + name
      optype = {
        self.EQ:  'IcmpInst::ICMP_EQ',
        self.NE:  'IcmpInst::ICMP_NE',
        self.UGT: 'IcmpInst::ICMP_UGT',
        self.UGE: 'IcmpInst::ICMP_UGE',
        self.ULT: 'IcmpInst::ICMP_ULT',
        self.ULE: 'IcmpInst::ICMP_ULE',
        self.SGT: 'IcmpInst::ICMP_SGT',
        self.SGE: 'IcmpInst::ICMP_SGE',
        self.SLT: 'IcmpInst::ICMP_SLT',
        self.SLE: 'IcmpInst::ICMP_SLE',        
      }[self.op]
      extra = ' && {0} == {1}'.format(opname, optype)
    
    context.addVar(opname, 'ICmpInstr::PredicateType')
    return 'match({name}, m_ICmp({pred}, {l}, {r})){extra}'.format(
      name = name,
      pred = opname,
      l = context.ref(self.v1),
      r = context.ref(self.v2),
      extra = extra
    )
      

################################
class Select(Instr):
  def __init__(self, type, c, v1, v2):
    assert isinstance(type, Type)
    assert isinstance(c, Value)
    assert isinstance(c.type, IntType)
    assert isinstance(v1, Value)
    assert isinstance(v2, Value)
    self.type = type.ensureFirstClass()
    self.c = c
    self.v1 = v1
    self.v2 = v2

  def __repr__(self):
    t = str(self.type)
    if len(t) > 0:
      t = t + ' '
    return 'select i1 %s, %s%s, %s%s' % (self.c.getName(), t, self.v1.getName(),
                                         t, self.v2.getName())

  def toSMT(self, poison, state, qvars):
    return [], If(state.eval(self.c, poison, qvars) == 1,
                  state.eval(self.v1, poison, qvars),
                  state.eval(self.v2, poison, qvars))

  def getTypeConstraints(self):
    return And(self.type == self.v1.type,
               self.type == self.v2.type,
               self.c.type == 1,
               self.type.getTypeConstraints())

  def getPatternMatch(self, context, name = None):
    if name == None: name = self.getCName()
    
    return 'match({0}, m_Select({1}, {2}, {3}))'.format(
      name,
      context.ref(self.c),
      context.ref(self.v1),
      context.ref(self.v2)
    )

################################
class Alloca(Instr):
  def __init__(self, type, elemsType, numElems, align):
    assert isinstance(elemsType, IntType)
    assert isinstance(align, int)
    self.type = PtrType(type)
    self.elemsType = elemsType
    self.numElems = TypeFixedValue(numElems, 1, 16)
    self.align = align

  def __repr__(self):
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

  def toSMT(self, poison, state, qvars):
    self.numElems.toSMT(poison, state, qvars)
    ptr = BitVec(self.getName(), self.type.getSize())
    block_size = getAllocSize(self.type.type)
    num_elems = self.numElems.getValue()
    size = num_elems * block_size

    if size == 0:
      return BoolVal(True), ptr

    defined = [ULT(ptr, ptr + (size >> 3)),
               ptr != 0,
               getPtrAlignCnstr(ptr, self.align)]

    mem = freshBV('alloca' + self.getName(), size)
    state.addAlloca(ptr, mem, (block_size, num_elems, self.align))
    return defined, ptr

  def getTypeConstraints(self):
    return And(self.numElems.getType() == self.elemsType,
               self.type.getTypeConstraints(),
               self.elemsType.getTypeConstraints(),
               self.numElems.getTypeConstraints())


################################
class GEP(Instr):
  def __init__(self, type, ptr, idxs, inbounds):
    assert isinstance(type, PtrType)
    assert isinstance(ptr, Value)
    assert isinstance(idxs, list)
    assert isinstance(inbounds, bool)
    for i in range(len(idxs)):
      assert isinstance(idxs[i], IntType if (i & 1) == 0 else Value)
    self.type = type
    self.ptr = ptr
    self.idxs = idxs[1:len(idxs):2]
    self.inbounds = inbounds

  def __repr__(self):
    inb = 'inbounds ' if self.inbounds else ''
    idxs = ''
    for i in range(len(self.idxs)):
      t = str(self.idxs[i].type)
      if len(t) > 0:
        t += ' '
      idxs += ', %s%s' % (t, self.idxs[i].getName())
    return 'getelementptr %s%s %s%s' % (inb, self.type, self.ptr.getName(),
                                        idxs)

  def toSMT(self, poison, state, qvars):
    ptr = state.eval(self.ptr, poison, qvars)
    type = self.type
    for i in range(len(self.idxs)):
      idx = truncateOrSExt(state.eval(self.idxs[i], poison, qvars), ptr)
      ptr += getAllocSize(type.getPointeeType())/8 * idx
      if i + 1 != len(self.idxs):
        type = type.getUnderlyingType()

    # TODO: handle inbounds
    return [], ptr

  def getTypeConstraints(self):
    return And(self.type.ensureTypeDepth(len(self.idxs)),
               Instr.getTypeConstraints(self))


################################
class Load(Instr):
  def __init__(self, stype, v, align):
    assert isinstance(stype, PtrType)
    assert isinstance(v, Value)
    assert isinstance(align, int)
    self.stype = stype
    stype.type = stype.type.ensureFirstClass()
    self.type = stype.type
    self.v = v
    self.align = align

  def __repr__(self):
    align = ', align %d' % self.align if self.align != 0 else ''
    return 'load %s %s%s' % (str(self.stype), self.v.getName(), align)

  def extractBV(self, BV, offset, size):
    old_size = BV.size()
    BV = BV << offset
    return Extract(old_size - 1, old_size - size, BV)

  def _recPtrLoad(self, l, v, defined, mustload, qvars):
    if len(l) == 0:
      return None

    (ptr, mem, qvs, info) = l[0]
    (block_size, num_elems, align) = info
    size = mem.size()
    read_size = self.type.getSize()
    actual_read_size = getAllocSize(self.type)

    if size > read_size:
      offset = truncateOrZExt((v - ptr) << 3, mem)
      mem = self.extractBV(mem, offset, read_size)
    elif size < read_size:
      # undef behavior; skip this block
      return self._recPtrLoad(l[1:], v, defined, mustload, qvars)

    inbounds = And(UGE(v, ptr), UGE((size - read_size)/8, v - ptr))
    mustload += [inbounds]
    qvars += qvs

    if self.align != 0:
      # overestimating the alignment is undefined behavior.
      defined += [Implies(inbounds, align >= self.align)]

    mem2 = self._recPtrLoad(l[1:], v, defined, mustload, qvars)
    return mem if mem2 is None else If(inbounds, mem, mem2)

  def toSMT(self, poison, state, qvars):
    v = state.eval(self.v, poison, qvars)
    defined = [v != 0]
    mustload = []
    val = self._recPtrLoad(state.ptrs, v, defined, mustload, qvars)
    defined += [mk_or(mustload)]
    return ([BoolVal(False)], 0) if val is None else (defined, val)

  def getTypeConstraints(self):
    return And(self.stype == self.v.type,
               self.type == self.v.type.getPointeeType(),
               self.type.getTypeConstraints())


################################
class Store(Instr):
  def __init__(self, stype, src, type, dst, align):
    assert isinstance(stype, Type)
    assert isinstance(src, Value)
    assert isinstance(type, PtrType)
    assert isinstance(dst, Value)
    assert isinstance(align, int)
    self.stype = stype.ensureFirstClass()
    self.src = src
    self.type = type
    self.dst = dst
    self.align = align
    self.setName('store')
    self.id = mk_unique_id()
    self.type.setName(self.getUniqueName())

  def getUniqueName(self):
    return self.getName() + '_' + self.id

  def __repr__(self):
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
    offset = (tgt - ptr) << 3
    new = LShR(truncateOrPad(src, mem), truncateOrZExt(offset, mem))

    # mask out bits that will be written
    mask = BitVecVal((1 << size) - 1, size)
    m1 = mask << truncateOrZExt(size - offset, mem)
    m2 = LShR(mask, truncateOrZExt(write_size + offset, mem))
    old = mem & (m1 | m2)
    return new | old

  def toSMT(self, poison, state, qvars):
    qvars_new = []
    src = state.eval(self.src, poison, qvars_new)
    tgt = state.eval(self.dst, poison, qvars_new)
    qvars += qvars_new
    defined = [tgt != 0]

    write_size = getAllocSize(self.stype)
    newmem = []
    mustwrite = []
    for (ptr, mem, qvs, info) in state.ptrs:
      (block_size, num_elems, align) = info
      size = block_size * num_elems
      # skip block if it is too small
      if size < write_size:
        newmem += [(ptr, mem, qvs, info)]
        continue

      inbounds = And(UGE(tgt, ptr), UGE((size - write_size)/8, tgt - ptr))
      mustwrite += [inbounds]

      writes = mk_and(state.defined + [inbounds])
      mem = If(writes, self._mkMem(src, tgt, ptr, size, mem), mem)
      qvs += qvars_new
      newmem += [(ptr, mem, qvs, (block_size, num_elems, align))]

      if self.align != 0:
        # overestimating the alignment is undefined behavior.
        defined += [Implies(inbounds, align >= self.align)]

    state.ptrs = newmem
    defined += [mk_or(mustwrite)]
    return defined, None

  def getTypeConstraints(self):
    return And(self.stype == self.type.type,
               self.src.type == self.stype,
               self.dst.type == self.type,
               self.stype.getTypeConstraints(),
               self.type.getTypeConstraints())


################################
class Skip(Instr):
  def __init__(self):
    self.id = mk_unique_id()

  def getUniqueName(self):
    return 'skip_' + self.id

  def __repr__(self):
    return 'skip'

  def toSMT(self, poison, state, qvars):
    return [BoolVal(True)], None


################################
class Unreachable(Instr):
  def __init__(self):
    self.id = mk_unique_id()

  def getUniqueName(self):
    return 'unreachable_' + self.id

  def __repr__(self):
    return 'unreachable'

  def toSMT(self, poison, state, qvars):
    return [BoolVal(False)], None


################################
class TerminatorInst(Instr):
  pass


################################
class Br(TerminatorInst):
  def __init__(self, bb_label, cond, true, false):
    assert isinstance(bb_label, str)
    assert isinstance(cond, Value)
    assert isinstance(true, str)
    assert isinstance(false, str)
    self.cond = cond
    self.true = true
    self.false = false
    self.setName('br_' + bb_label)

  def __repr__(self):
    return "br i1 %s, label %s, label %s" % (self.cond.getName(),
                                             self.true, self.false)

  def getSuccessors(self, state):
    poison = []
    qvars = []
    cond = state.eval(self.cond, poison, qvars)
    assert qvars == []
    return [(self.true, mk_and([cond != 0] + state.defined + poison)),
            (self.false, mk_and([cond == 0] + state.defined + poison))]

  def toSMT(self, poison, state, qvars):
    return [BoolVal(True)], None


################################
class Ret(TerminatorInst):
  def __init__(self, bb_label, type, val):
    assert isinstance(bb_label, str)
    assert isinstance(type, Type)
    assert isinstance(val, Value)
    self.type = type
    self.val = val
    self.setName('ret_' + bb_label)

  def __repr__(self):
    t = str(self.type)
    if len(t) > 0:
      t = t + ' '
    return "ret %s%s" % (t, self.val.getName())

  def getSuccessors(self, state):
    return []

  def toSMT(self, poison, state, qvars):
    return [BoolVal(True)], state.eval(self.val, poison, qvars)

  def getTypeConstraints(self):
    return And(self.type == self.val.type, self.type.getTypeConstraints())


################################
def print_prog(p):
  for bb, instrs in p.iteritems():
    if bb != "":
      print "%s:" % bb

    for k,v in instrs.iteritems():
      k = str(k)
      if k[0] == '%':
        print '  %s = %s' % (k, v)
      else:
        print "  %s" % v


def countUsers(prog):
  m = {}
  for bb, instrs in prog.iteritems():
    for k, v in instrs.iteritems():
      v.countUsers(m)
  return m


def getTypeConstraints(p):
  t = [v.getTypeConstraints() for v in p.itervalues()]
  # ensure all return instructions have the same type
  ret_types = [v.type for v in p.itervalues() if isinstance(v, Ret)]
  if len(ret_types) > 1:
    t += mkTyEqual(ret_types)
  return t


def fixupTypes(p, types):
  for v in p.itervalues():
    v.fixupTypes(types)


def toSMT(prog, idents, isSource):
  set_smt_is_source(isSource)
  state = State()
  for k,v in idents.iteritems():
    if isinstance(v, (Input, Constant)):
      poison = []
      qvars = []
      defined, smt = v.toSMT(poison, state, qvars)
      assert defined == [] and poison == []
      state.add(v, smt, [], [], qvars)

  for bb, instrs in prog.iteritems():
    state.newBB(bb)
    for k,v in instrs.iteritems():
      poison = []
      qvars = []
      defined, smt = v.toSMT(poison, state, qvars)
      state.add(v, smt, defined, poison, qvars)
  return state
