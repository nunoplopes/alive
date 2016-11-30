# Copyright 2014-2016 The Alive authors.
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
from codegen import *


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


def defined_align_access(defined, align, ptr, poison):
  defined.append(ptr != 0)
  defined.append(poison != -1)
  # FIXME: ABI-defined
  if align == 0:
    align = 4

  if align == 1:
    return

  align = (int)(math.log(align, 2))
  defined.append(Extract(align-1, 0, ptr) == 0)


def mk_undef_var(qvars, size):
  qv = BitVec('undef' + mk_unique_id(), size)
  qvars.append(qv)
  return qv


def freeze(v, p, qvars):
  if p.eq(BitVecVal(0, p.size())):
    return v
  return (v & ~p) | (mk_undef_var(qvars, v.size()) & p)


################################
class State:
  def __init__(self):
    self.vars = collections.OrderedDict()
    self.defined = [] # definedness so far in the BB
    self.qvars = []
    self.allocas = []
    self.accessed_ptrs = set([])
    self.mem_qvars = []
    self.bb_pres = {}
    self.bb_qvars = {}
    self.bb_mem = {}

  def add(self, v, smt, defined, qvars):
    if v.getUniqueName() == '':
      return
    self.vars[v.getUniqueName()] = (smt, self.defined + defined, qvars)
    if isinstance(v, TerminatorInst):
      for (bb,cond,qvars) in v.getSuccessors(self):
        bb = bb[1:]
        cond = mk_and([cond] + self.defined)
        if bb not in self.bb_pres:
          self.bb_pres[bb] = []
          self.bb_qvars[bb] = []
          self.bb_mem[bb] = []
        self.bb_pres[bb] += [cond]
        self.bb_qvars[bb] += qvars
        self.bb_mem[bb].append((cond, (self.mem, self.mem_poison)))

  def addAlloca(self, ptr, size):
    self.mem_qvars.append(ptr)
    self.allocas.append((ptr, size))

  def store_bit(self, dst, val, poison):
    if use_array_theory():
      self.mem = Update(self.mem, dst, val)
      self.mem_poison = Update(self.mem_poison, dst, poison)
    else:
      self.mem = If(self.idx_var == dst, val, self.mem)
      self.mem_poison = If(self.idx_var == dst, poison, self.mem_poison)

  def store(self, dst, val, bits, defined):
    self.defined += defined
    self.accessed_ptrs.add((dst, bits))
    dst = Concat(dst, BitVecVal(0, 3))
    src, srcpoison = val
    for i in range(0, bits):
      # little-endian
      self.store_bit(dst + i, Extract(i, i, src), Extract(i, i, srcpoison))

  def load_bit(self, ptr):
    if use_array_theory():
      return self.mem[ptr], self.mem_poison[ptr]
    return substitute(self.mem, (self.idx_var, ptr)),\
           substitute(self.mem_poison, (self.idx_var, ptr))

  def load(self, ptr, bits, defined):
    self.defined += defined
    self.accessed_ptrs.add((ptr, bits))
    val, poison = [], []
    ptr = Concat(ptr, BitVecVal(0, 3))
    for i in range(bits):
      valb, poisonb = self.load_bit(ptr + i)
      # little-endian
      val.insert(0, valb)
      poison.insert(0, poisonb)
    return simplify(mk_concat(val)), simplify(mk_concat(poison))

  def newBB(self, name):
    if name in self.bb_pres:
      self.defined = [mk_or(self.bb_pres[name])]
      self.qvars = self.bb_qvars[name]
      self.mem, self.mem_poison = fold_ite_list2(self.bb_mem[name])
    else:
      self.defined = []
      self.qvars = []
      if use_array_theory():
        self.mem = Array('mem0', BitVecSort(get_ptr_size() + 3), BitVecSort(1))
        self.mem_poison = Array('mem_poison0',
                                BitVecSort(get_ptr_size() + 3), BitVecSort(1))
      else:
        self.idx_var = BitVec('idx', get_ptr_size() + 3)
        self.mem = Function('mem0', BitVecSort(get_ptr_size() + 3),
                            BitVecSort(1))(self.idx_var)
        self.mem_poison = Function('mem_poison0',
                                   BitVecSort(get_ptr_size() + 3),
                                   BitVecSort(1))(self.idx_var)
    self.current_bb = name

  def getAllocaConstraints(self):
    if self.allocas == []:
      return []

    cnstr = []
    # 1) Alloca ptrs are never null
    for (ptr, size) in self.allocas:
      if size > 0:
        cnstr.append(ptr != 0)

    # 2) Input pointers cannot guess alloca ptr values
    for (ptr, size) in self.accessed_ptrs:
      ptr = simplify(ptr)
      ptrs = str(ptr)
      for (ptra, sizea) in self.allocas:
        ptra = str(ptra)
        if ptrs.find(ptra) == -1:
          cnstr.append(Or(UGE(ptra, ptr + size),
                          ULE(ptra + sizea, ptr)))
    return cnstr

  def eval(self, v, defined, qvars):
    (v,u), d, q = self.vars[v.getUniqueName()]
    defined += d
    qvars += self.qvars + q
    return v, u

  def items(self):
    for k,v in self.vars.items():
      if k[0] != '%' and k[0] != 'C' and not k.startswith('ret_'):
        continue
      yield k,v

  def __contains__(self, k):
    return k in self.vars

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

  def toSMT(self, defined, state, qvars):
    return state.eval(self.v, defined, qvars)

  def getTypeConstraints(self):
    return And(self.type == self.v.type,
               self.type.getTypeConstraints())

  def register_types(self, manager):
    manager.register_type(self, self.type, UnknownType())
    manager.unify(self, self.v)

  # TODO: visit_source?

  def visit_target(self, manager, use_builder=False):
    instr = manager.get_cexp(self.v)

    if use_builder:
      isntr = CVariable('Builder').arr('Insert', [instr])

    # TODO: this probably should use manager.get_ctype,
    # but that currently doesn't distinguish source instructions (Value)
    # from target instructions (Instruction)
    if isinstance(self.v, Instr):
      ctype = manager.PtrInstruction
    else:
      ctype = manager.PtrValue

    return [CDefinition.init(
      ctype,
      manager.get_cexp(self),
      instr)]


################################
class Freeze(Instr):
  def __init__(self, v, type):
    self.v = v
    self.type = type
    assert isinstance(self.v, Value)
    assert isinstance(self.type, Type)

  def __repr__(self):
    s = 'freeze '
    t = str(self.type)
    if len(t) > 0:
      s += t + ' '
    return s + self.v.getName()

  def toSMT(self, defined, state, qvars):
    v,p = state.eval(self.v, defined, qvars)
    return freeze(v, p, qvars), BitVecVal(0, v.size())

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
    self.flags = list(flags)
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

  def _genPoisonConds(self, v1, v2, p1, p2, qvars):
    undef_conds = {
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

    undef = []
    if do_infer_flags():
      for flag,fn in undef_conds.items():
        bit = get_flag_var(flag, self.getName())
        undef += [Implies(bit == 1,
                          fn(freeze(v1, p1, qvars), freeze(v2, p2, qvars)))]
    else:
      for f in self.flags:
        undef += [undef_conds[f](freeze(v1, p1, qvars), freeze(v2, p2, qvars))]
    return undef

  def _genSMTDefConds(self, a, b, p1, p2, bits):
    # definedness of the instruction
    if bits > 1:
      a_not_intmin = lambda : [Extract(bits-2, 0, a & ~p1) != 0,
                               Extract(bits-1, bits-1, a | p1) == 0]
    else:
      a_not_intmin = lambda : [(a | p1) == 0]
    return {
      self.Add:  lambda: [],
      self.Sub:  lambda: [],
      self.Mul:  lambda: [],
      self.UDiv: lambda: [b & ~p2 != 0],
      self.SDiv: lambda: [b & ~p2 != 0, Or(a_not_intmin() + [(b | p2) != -1])],
      self.URem: lambda: [b & ~p2 != 0],
      self.SRem: lambda: [b & ~p2 != 0, Or(a_not_intmin() + [(b | p2) != -1])],
      self.Shl:  lambda: [],
      self.AShr: lambda: [],
      self.LShr: lambda: [],
      self.And:  lambda: [],
      self.Or:   lambda: [],
      self.Xor:  lambda: [],
      }[self.op]()

  def _poisonPropagation(self, a, b, p1, p2, fn, qvars):
    generic = lambda u1 = mk_undef_var(qvars, a.size()), \
                     u2 = mk_undef_var(qvars, b.size()) : \
      (fn(freeze(a, p1, qvars), u1)[0] ^ fn(freeze(a, p1, qvars), u1)[0]) | \
      (fn(u2, freeze(b, p2, qvars))[0] ^ fn(u2, freeze(b, p2, qvars))[0])
    return {
      self.Add:  generic,
      self.Sub:  generic,
      self.Mul:  generic,
      self.UDiv: generic,
      self.SDiv: generic,
      self.URem: generic,
      self.SRem: generic,
      self.Shl:  generic,
      self.AShr: generic,
      self.LShr: generic,
      self.And:  generic,
      self.Or:   generic,
      self.Xor:  generic,
      }[self.op]()

  def toSMT(self, defined, state, qvars):
    bits = self.type.getSize()
    v1, p1 = state.eval(self.v1, defined, qvars)
    v2, p2 = state.eval(self.v2, defined, qvars)
    nonpoison = self._genPoisonConds(v1, v2, p1, p2, qvars)
    defined += self._genSMTDefConds(v1, v2, p1, p2, bits)
    fn = {
      self.Add:  lambda a,b: (a + b, []),
      self.Sub:  lambda a,b: (a - b, []),
      self.Mul:  lambda a,b: (a * b, []),
      self.UDiv: lambda a,b: (UDiv(a, b), []),
      self.SDiv: lambda a,b: (a / b, []),
      self.URem: lambda a,b: (URem(a, b), []),
      self.SRem: lambda a,b: (SRem(a, b), []),
      self.Shl:  lambda a,b: (a << b, [ULT(b | p2, bits)]),
      self.AShr: lambda a,b: (a >> b, [ULT(b | p2, bits)]),
      self.LShr: lambda a,b: (LShR(a, b), [ULT(b | p2, bits)]),
      self.And:  lambda a,b: (a & b, []),
      self.Or:   lambda a,b: (a | b, []),
      self.Xor:  lambda a,b: (a ^ b, []),
    }[self.op]
    val, extranonpoison = fn(v1, v2)
    return val, mk_if(mk_and(nonpoison + extranonpoison),
                      self._poisonPropagation(v1, v2, p1, p2, fn, qvars),
                      BitVecVal(-1, bits))

  def getTypeConstraints(self):
    return And(self.type == self.v1.type,
               self.type == self.v2.type,
               self.type.getTypeConstraints())

  caps = {
    Add:  'Add',
    Sub:  'Sub',
    Mul:  'Mul',
    UDiv: 'UDiv',
    SDiv: 'SDiv',
    URem: 'URem',
    SRem: 'SRem',
    Shl:  'Shl',
    AShr: 'AShr',
    LShr: 'LShr',
    And:  'And',
    Or:   'Or',
    Xor:  'Xor',
  }

  def register_types(self, manager):
    manager.register_type(self, self.type, IntType())
    manager.unify(self, self.v1, self.v2)

  def visit_source(self, mb):
    r1 = mb.subpattern(self.v1)
    r2 = mb.subpattern(self.v2)

    op = BinOp.caps[self.op]

    if 'nsw' in self.flags and 'nuw' in self.flags:
      return CFunctionCall('match',
        mb.get_my_ref(),
        CFunctionCall('m_CombineAnd',
          CFunctionCall('m_NSW' + op, r1, r2),
          CFunctionCall('m_NUW' + op,
            CFunctionCall('m_Value'),
            CFunctionCall('m_Value'))))

    if 'nsw' in self.flags:
      return mb.simple_match('m_NSW' + op, r1, r2)

    if 'nuw' in self.flags:
      return mb.simple_match('m_NUW' + op, r1, r2)

    if 'exact' in self.flags:
      return CFunctionCall('match',
        mb.get_my_ref(),
        CFunctionCall('m_Exact', CFunctionCall('m_' + op, r1, r2)))

    return mb.simple_match('m_' + op, r1, r2)

  def visit_target(self, manager, use_builder=False):
    cons = CFunctionCall('BinaryOperator::Create' + self.caps[self.op],
      manager.get_cexp(self.v1), manager.get_cexp(self.v2))

    if use_builder:
      cons = CVariable('Builder').arr('Insert', [cons])

    gen = [CDefinition.init(CPtrType(CTypeName('BinaryOperator')), manager.get_cexp(self), cons)]

    for f in self.flags:
      setter = {'nsw': 'setHasNoSignedWrap', 'nuw': 'setHasNoUnsignedWrap', 'exact': 'setIsExact'}[f]
      gen.append(manager.get_cexp(self).arr(setter, [CVariable('true')]))

    return gen


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

  def toSMT(self, defined, state, qvars):
    v, p = state.eval(self.v, defined, qvars)
    fn = {
      self.Trunc:       lambda v: Extract(self.type.getSize()-1, 0, v),
      self.ZExt:        lambda v: ZeroExt(self.type.getSize() -
                                         self.stype.getSize(), v),
      self.SExt:        lambda v: SignExt(self.type.getSize() -
                                          self.stype.getSize(), v),
      self.ZExtOrTrunc: lambda v: truncateOrZExt(v, self.type.getSize()),
      self.Ptr2Int:     lambda v: truncateOrZExt(v, self.type.getSize()),
      self.Int2Ptr:     lambda v: truncateOrZExt(v, self.type.getSize()),
      self.Bitcast:     lambda v: v,
    }[self.op]
    return fn(v), fn(p)

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

  matcher = {
    Trunc:   'm_Trunc',
    ZExt:    'm_ZExt',
    SExt:    'm_SExt',
    Ptr2Int: 'm_PtrToInt',
    Bitcast: 'm_BitCast',
  }


  constr = {
    Trunc:   'TruncInst',
    ZExt:    'ZExtInst',
    SExt:    'SExtInst',
    Ptr2Int: 'PtrToIntInst',
    Int2Ptr: 'IntToPtrInst',
    Bitcast: 'BitCastInst',
  }

  def register_types(self, manager):
    if self.enforceIntSrc(self.op):
      manager.register_type(self.v, self.stype, IntType())
    elif self.enforcePtrSrc(self.op):
      manager.register_type(self.v, self.stype, PtrType())
    else:
      manager.register_type(self.v, self.stype, UnknownType())

    if self.enforceIntTgt(self.op):
      manager.register_type(self, self.type, IntType())
    elif self.enforcePtrTgt(self.op):
      manager.register_type(self, self.type, PtrType())
    else:
      manager.register_type(self, self.type, UnknownType())
    # TODO: inequalities for trunc/sext/zext

  def visit_source(self, mb):
    r = mb.subpattern(self.v)

    if self.op == ConversionOp.ZExtOrTrunc:
      return CFunctionCall('match',
        mb.get_my_ref(),
        CFunctionCall('m_CombineOr',
          CFunctionCall('m_ZExt', r),
          CFunctionCall('m_ZTrunc', r)))

    return mb.simple_match(ConversionOp.matcher[self.op], r)

  def visit_target(self, manager, use_builder=False):
    if self.op == ConversionOp.ZExtOrTrunc:
      assert use_builder  #TODO: handle ZExtOrTrunk in root position
      instr = CVariable('Builder').arr('CreateZExtOrTrunc',
        [manager.get_cexp(self.v), manager.get_llvm_type(self)])
      return [CDefinition.init(
        manager.PtrValue,
        manager.get_cexp(self),
        instr)]

    else:
      instr = CFunctionCall('new ' + ConversionOp.constr[self.op],
        manager.get_cexp(self.v), manager.get_llvm_type(self))

      if use_builder:
        instr = CVariable('Builder').arr('Insert', [instr])

    return [CDefinition.init(
      manager.PtrInstruction,
      manager.get_cexp(self),
      instr)]


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

  def getOpName(self):
    return 'icmp'

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
      self.EQ:  lambda : a == b,
      self.NE:  lambda : a != b,
      self.UGT: lambda : UGT(a, b),
      self.UGE: lambda : UGE(a, b),
      self.ULT: lambda : ULT(a, b),
      self.ULE: lambda : ULE(a, b),
      self.SGT: lambda : a > b,
      self.SGE: lambda : a >= b,
      self.SLT: lambda : a < b,
      self.SLE: lambda : a <= b,
    }[op]()

  def recurseSMT(self, ops, a, b, i):
    if len(ops) == 1:
      return self.opToSMT(ops[0], a, b)
    opname = self.opname if self.opname != '' else self.getName()
    var = BitVec('icmp_' + opname, 4)
    assert 1 << 4 > self.Var
    return If(var == i,
              self.opToSMT(ops[0], a, b),
              self.recurseSMT(ops[1:], a, b, i+1))

  def toSMT(self, defined, state, qvars):
    # Generate all possible comparisons if icmp is generic. Set of comparisons
    # can be restricted in the precondition.
    ops = [self.op] if self.op != self.Var else range(self.Var)
    v1, p1 = state.eval(self.v1, defined, qvars)
    v2, p2 = state.eval(self.v2, defined, qvars)
    fn = lambda a,b : self.recurseSMT(ops, a, b, 0)
    r1 = fn(freeze(v1, p1, qvars), freeze(v2, p2, qvars))
    r2 = fn(freeze(v1, p1, qvars), freeze(v2, p2, qvars))
    return toBV(fn(v1, v2)), toBV(Or(p1 == -1, p2 == -1, r1 != r2))
    #u1 = mk_undef_var(qvars, v1.size())
    #u2 = mk_undef_var(qvars, v2.size())
    #u1 = fn(freeze(v1, p1, qvars), u1) != fn(freeze(v1, p1, qvars), u1)
    #u2 = fn(u2, freeze(v2, p2, qvars)) != fn(u2, freeze(v2, p2, qvars))
    #return toBV(fn(v1, v2)), toBV(Or(p1 == -1, p2 == -1, u1, u2))

  def getTypeConstraints(self):
    return And(self.stype == self.v1.type,
               self.stype == self.v2.type,
               self.type.getTypeConstraints(),
               self.stype.getTypeConstraints())

  op_enum = {
    EQ:  'ICmpInst::ICMP_EQ',
    NE:  'ICmpInst::ICMP_NE',
    UGT: 'ICmpInst::ICMP_UGT',
    UGE: 'ICmpInst::ICMP_UGE',
    ULT: 'ICmpInst::ICMP_ULT',
    ULE: 'ICmpInst::ICMP_ULE',
    SGT: 'ICmpInst::ICMP_SGT',
    SGE: 'ICmpInst::ICMP_SGE',
    SLT: 'ICmpInst::ICMP_SLT',
    SLE: 'ICmpInst::ICMP_SLE',
  }

  def register_types(self, manager):
    manager.register_type(self, self.type, IntType(1))
    manager.register_type(self.v1, self.stype, UnknownType().ensureIntPtrOrVector())
    manager.unify(self.v1, self.v2)

  PredType = CTypeName('CmpInst::Predicate')

  def visit_source(self, mb):
    r1 = mb.subpattern(self.v1)
    r2 = mb.subpattern(self.v2)

    if self.op == Icmp.Var:
      opname = self.opname if self.opname else 'Pred ' + self.name
      name = mb.manager.get_key_name(opname)  #FIXME: call via mb?
      rp = mb.binding(name, self.PredType)

      return mb.simple_match('m_ICmp', rp, r1, r2)

    pvar = mb.new_name('P')
    rp = mb.binding(pvar, self.PredType)

    return CBinExpr('&&',
      mb.simple_match('m_ICmp', rp, r1, r2),
      CBinExpr('==', CVariable(pvar), CVariable(Icmp.op_enum[self.op])))

  def visit_target(self, manager, use_builder=False):

    # determine the predicate
    if self.op == Icmp.Var:
      key = self.opname if self.opname else 'Pred ' + self.name
      opname = manager.get_key_name(key)
      assert manager.bound(opname)
      # TODO: confirm type

    else:
      opname = Icmp.op_enum[self.op]

    instr = CFunctionCall('new ICmpInst', CVariable(opname),
      manager.get_cexp(self.v1), 
      manager.get_cexp(self.v2))

    if use_builder:
      instr = CVariable('Builder').arr('Insert', [instr])

    return [
      CDefinition.init(manager.PtrInstruction, manager.get_cexp(self), instr)]


################################
class Select(Instr):
  def __init__(self, type, c, v1, v2):
    assert isinstance(type, Type)
    assert isinstance(c, Value)
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

  def getOpName(self):
    return 'select'

  def toSMT(self, defined, state, qvars):
    c, uc = state.eval(self.c, defined, qvars)
    c = (c == 1)
    v1, u1 = state.eval(self.v1, defined, qvars)
    v2, u2 = state.eval(self.v2, defined, qvars)
    return mk_if(c, v1, v2), mk_if(uc == 1, BitVecVal(-1, v1.size()),
                                            mk_if(c, u1, u2))

  def getTypeConstraints(self):
    return And(self.type == self.v1.type,
               self.type == self.v2.type,
               self.c.type == 1,
               self.type.getTypeConstraints())

  def register_types(self, manager):
    manager.register_type(self, self.type, UnknownType().ensureFirstClass())
    manager.register_type(self.c, self.c.type, IntType(1))
    manager.unify(self, self.v1, self.v2)

  def visit_source(self, mb):
    c = mb.subpattern(self.c)
    v1 = mb.subpattern(self.v1)
    v2 = mb.subpattern(self.v2)

    return mb.simple_match('m_Select', c, v1, v2)

  def visit_target(self, manager, use_builder=False):
    instr = CFunctionCall('SelectInst::Create',
      manager.get_cexp(self.c),
      manager.get_cexp(self.v1),
      manager.get_cexp(self.v2))

    if use_builder:
      instr = CVariable('Builder').arr('Insert', [instr])

    return [CDefinition.init(manager.PtrInstruction, manager.get_cexp(self), instr)]

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

  def getOpName(self):
    return 'alloca'

  def toSMT(self, defined, state, qvars):
    self.numElems.toSMT(defined, state, qvars)
    ptr = BitVec(self.getName(), self.type.getSize())
    block_size = getAllocSize(self.type.type)
    num_elems = self.numElems.getValue()
    size = num_elems * block_size

    if size == 0:
      qvars.append(ptr)
      return ptr, BitVecVal(-1, self.type.getSize())

    if size > 8:
      defined.append(ULE(ptr, -(size >> 3)))
    defined += [ptr != 0,
                getPtrAlignCnstr(ptr, self.align)]

    state.addAlloca(ptr, size)
    return ptr, BitVecVal(0, self.type.getSize())

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

  def getOpName(self):
    return 'getelementptr'

  def toSMT(self, defined, state, qvars):
    undef = []
    ptr, u = state.eval(self.ptr, defined, qvars)
    undef.append(u)
    type = self.type
    for i in range(len(self.idxs)):
      idx, u = state.eval(self.idxs[i], defined, qvars)
      ## FIXME undef.append(u)
      idx = truncateOrSExt(idx, ptr)
      ptr += getAllocSize(type.getPointeeType())/8 * idx
      if i + 1 != len(self.idxs):
        type = type.getUnderlyingType()

    # TODO: handle inbounds
    #FIXME poison
    return ptr, BitVecVal(0, ptr.size())

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

  def getOpName(self):
    return 'load'

  def toSMT(self, defined, state, qvars):
    qvars += state.mem_qvars
    ptr, poison = state.eval(self.v, defined, qvars)
    access_sz = getAllocSize(self.type)
    defined_align_access(defined, self.align, ptr, poison)
    return state.load(ptr, self.type.getSize(), defined)

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

  def getOpName(self):
    return 'store'

  def __repr__(self):
    t = str(self.stype)
    if len(t) > 0:
      t = t + ' '
    align = ', align %d' % self.align if self.align != 0 else ''
    return 'store %s%s, %s %s%s' % (t, self.src.getName(), str(self.type),
                                    self.dst.getName(), align)

  def toSMT(self, defined, state, qvars):
    qvars_new = []
    src = state.eval(self.src, defined, qvars_new)
    tgt, ptgt = state.eval(self.dst, defined, qvars_new)
    qvars += qvars_new
    state.mem_qvars += qvars_new

    write_size = getAllocSize(self.stype)
    defined_align_access(defined, self.align, tgt, ptgt)
    state.store(tgt, src, self.stype.getSize(), defined)
    return None, None

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

  def toSMT(self, defined, state, qvars):
    return None, None


################################
class Unreachable(Instr):
  def __init__(self):
    self.id = mk_unique_id()

  def getUniqueName(self):
    return 'unreachable_' + self.id

  def __repr__(self):
    return 'unreachable'

  def toSMT(self, defined, state, qvars):
    defined.append(BoolVal(False))
    return None, None


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
    defined = []
    qvars = []
    cond, poison = state.eval(self.cond, defined, qvars)
    poison = poison == 0
    return [(self.true, mk_and([cond != 0, poison] + defined), qvars),
            (self.false, mk_and([cond == 0, poison] + defined), qvars)]

  def toSMT(self, defined, state, qvars):
    return None, None


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

  def toSMT(self, defined, state, qvars):
    return state.eval(self.val, defined, qvars)

  def getTypeConstraints(self):
    return And(self.type == self.val.type, self.type.getTypeConstraints())


################################
def print_prog(p, skip):
  for bb, instrs in p.items():
    if bb != "":
      print("%s:" % bb)

    for k,v in instrs.items():
      if k in skip:
        continue
      k = str(k)
      if k[0] == '%':
        print('  %s = %s' % (k, v))
      else:
        print("  %s" % v)


def countUsers(prog):
  m = {}
  for bb, instrs in prog.items():
    for k, v in instrs.items():
      v.countUsers(m)
  return m


def getTypeConstraints(p):
  t = [v.getTypeConstraints() for v in p.values()]
  # ensure all return instructions have the same type
  ret_types = [v.type for v in p.values() if isinstance(v, Ret)]
  if len(ret_types) > 1:
    t += mkTyEqual(ret_types)
  return t


def fixupTypes(p, types):
  for v in p.values():
    v.fixupTypes(types)


def toSMT(prog, idents, isSource):
  set_smt_is_source(isSource)
  state = State()
  for k,v in idents.items():
    if isinstance(v, (Input, Constant)):
      defined = []
      qvars = []
      smt = v.toSMT(defined, state, qvars)
      state.add(v, smt, defined, qvars)

  for bb, instrs in prog.items():
    state.newBB(bb)
    for k,v in instrs.items():
      defined = []
      qvars = []
      smt = v.toSMT(defined, state, qvars)
      state.add(v, smt, defined, qvars)
  return state
