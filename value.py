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

import copy, operator
from common import *
from codegen import CVariable, CFieldAccess


def allTyEqual(vars, Ty):
  c = [vars[0].type.typevar == Ty]
  for i in range(1, len(vars)):
    c += [vars[0].type == vars[i].type]
  return c



class Type:
  Int, Ptr, Array, Unknown = range(4)

  def __repr__(self):
    return ''

  def typeMismatch(self, expected):
    raise ParseError('%s type required' % expected, str(self))

  def ensureIntType(self, size = None):
    self.typeMismatch('int')

  def ensurePtrType(self):
    self.typeMismatch('pointer')

  def ensureFirstClass(self):
    self.typeMismatch('first class')

  def ensureIntPtrOrVector(self):
    self.typeMismatch('int/ptr/vector')


################################
def getMostSpecificType(t1, t2):
  def _ErrorOnTypeMismatch(cond):
    if cond:
      raise ParseError('Type mismatch: %s vs %s' % (t1, t2))

  if isinstance(t1, UnknownType):
    return t2
  if isinstance(t2, UnknownType):
    return t1
  _ErrorOnTypeMismatch(t1.__class__ != t2.__class__)

  if isinstance(t1, IntType):
    _ErrorOnTypeMismatch(t1.defined and t2.defined and
                         t1.getSize() != t2.getSize())
    return t1 if t1.defined else t2
  if isinstance(t1, PtrType):
    t1id = id(t1.type)
    return t1 if id(getMostSpecificType(t1.type, t2.type)) == t1id else t2
  assert False


################################
class UnknownType(Type):
  def __init__(self, d = 0):
    self.types = {self.Int: IntType(),
                  self.Ptr: PtrType(depth = d),
                  self.Array: ArrayType(depth = d),
                 }
    self.myType = self.Unknown

  def ensureIntType(self, size = None):
    return IntType(size)

  def ensurePtrType(self):
    return PtrType()

  def ensureFirstClass(self):
    # Restrict to ints, pointers, FPs, vectors
    del self.types[self.Array]
    return self

  def ensureIntPtrOrVector(self):
    # only ints, ptrs, or vectors of ints/ptrs
    del self.types[self.Array]
    return self

  def setName(self, name):
    self.typevar = Int('t_' + name)
    for t in self.types.itervalues():
      t.setName(name)

  def _getSizeUnknown(self, idx):
    if idx == len(self.types)-1:
      return self.types[idx].getSize()
    return If(self.typevar == idx,
              self.types[idx].getSize(),
              self._getSizeUnknown(idx+1))

  def getSize(self):
    if self.myType != self.Unknown:
      return self.types[self.myType].getSize()
    return self._getSizeUnknown(0)

  def getIntType(self, c):
    if self.myType == self.Unknown and self.types.has_key(self.Int):
      self.myType = self.Int
      c += [self.typevar == self.Int]

    if self.myType == self.Int:
      return self.types[self.Int]
    return None

  def getPointeeType(self):
    assert self.myType == self.Unknown or self.myType == self.Ptr
    self.myType = self.Ptr
    return self.types[self.Ptr].getPointeeType()

  def getUnderlyingType(self):
    assert self.myType == self.Ptr or self.myType == self.Array
    return self.types[self.myType].getUnderlyingType()

  def fixupTypes(self, types):
    self.myType = types.evaluate(self.typevar).as_long()
    self.types[self.myType].fixupTypes(types)

  def __eq__(self, other):
    if self.myType != self.Unknown:
      return And(self.typevar == self.myType,
                 self.types[self.myType] == other)

    for i,type in self.types.iteritems():
      if isinstance(other, type.__class__):
        self.myType = i
        return And(self.typevar == i, type == other)

    assert isinstance(other, UnknownType)
    c = []
    for i,type in self.types.iteritems():
      if other.types.has_key(i):
        c += [And(self.typevar == i,
                  other.typevar == i,
                  type == other.types[i])]
    return mk_or(c)

  def _intcmp(self, op, other):
    c = []
    op1 = self.getIntType(c)
    if op1 is None:
      return BoolVal(False)
    return mk_and(c + [op(op1, other)])

  def __lt__(self, other):
    return self._intcmp(operator.lt, other)

  def __gt__(self, other):
    return self._intcmp(operator.gt, other)

  def __ge__(self, other):
    return self._intcmp(operator.ge, other)

  def ensureTypeDepth(self, depth):
    c = []
    for i in range(len(self.types)):
      c += [Or(self.types[i].ensureTypeDepth(depth), self.typevar != i)]
    return mk_and(c)

  def getTypeConstraints(self):
    if self.myType != self.Unknown:
      return self.types[self.myType].getTypeConstraints()
    return mk_or([t.getTypeConstraints() for t in self.types.itervalues()])


################################
class NamedType(UnknownType):
  def __init__(self, name):
    UnknownType.__init__(self)
    self.type = UnknownType()
    self.name = name

  def __repr__(self):
    return self.name

  def ensureIntType(self, size = None):
    self.myType = self.Int
    if size != None:
      self.types[self.Int] = IntType(size)
    self.type = self.type.ensureIntType(size)
    return self

  def ensurePtrType(self):
    self.myType = self.Ptr
    self.type = self.type.ensurePtrType()
    return self

  def setName(self, name):
    UnknownType.setName(self, self.name)
    self.type.setName(name)

  def getTypeConstraints(self):
    return And(self.type == self,
               UnknownType.getTypeConstraints(self),
               self.type.getTypeConstraints())


################################
class IntType(Type):
  def __init__(self, size = None):
    if size == None:
      self.defined = False
      return
    self.size = size
    self.defined = True
    assert isinstance(self.size, int)

  def ensureIntType(self, size = None):
    assert self.defined == False or size == None or size == self.size
    if size != None:
      self.size = size
      self.defined = True
    return self

  def ensureFirstClass(self):
    return self

  def ensureIntPtrOrVector(self):
    return self

  def setName(self, name):
    self.typevar = Int('t_' + name)
    self.bitsvar = Int('size_' + name)

  def __repr__(self):
    if self.defined:
      return 'i' + str(self.size)
    return ''

  def getSize(self):
    if hasattr(self, 'size'):
      return self.size
    return self.bitsvar

  def fixupTypes(self, types):
    size = types.evaluate(self.bitsvar).as_long()
    assert self.defined == False or self.size == size
    self.size = size

  def __eq__(self, other):
    if isinstance(other, IntType):
      return self.bitsvar == other.bitsvar
    if isinstance(other, int):
      return self.bitsvar == other
    if isinstance(other, UnknownType):
      return other == self
    return BoolVal(False)

  def _cmp(self, op, other):
    if isinstance(other, IntType):
      return op(self.bitsvar, other.bitsvar)
    if isinstance(other, int):
      return op(self.bitsvar, other)
    if isinstance(other, UnknownType):
      c = []
      op2 = other.getIntType(c)
      return mk_and(c + [op(self.bitsvar, op2.bitsvar)])
    assert False

  def __lt__(self, other):
    return self._cmp(operator.lt, other)

  def __gt__(self, other):
    return self._cmp(operator.gt, other)

  def __ge__(self, other):
    return self._cmp(operator.ge, other)

  def ensureTypeDepth(self, depth):
    return BoolVal(depth == 0)

  def getTypeConstraints(self):
    # Integers are assumed to be up to 64 bits.
    c = [self.typevar == Type.Int, self.bitsvar > 0, self.bitsvar <= 64]
    if self.defined:
      c += [self.bitsvar == self.getSize()]
    return And(c)


################################
class PtrType(Type):
  def __init__(self, type = None, depth = 0):
    if type is None:
      # limit type nesting to 1 level
      if depth >= 0:
        type = IntType()
      else:
        type = UnknownType(depth+1)
    self.type = type
    assert isinstance(self.type, Type)

  def ensurePtrType(self):
    return self

  def ensureFirstClass(self):
    return self

  def ensureIntPtrOrVector(self):
    return self

  def __repr__(self):
    return str(self.type) + '*'

  def setName(self, name):
    self.typevar = Int('t_' + name)
    self.type.setName('*' + name)

  def getSize(self):
    if hasattr(self, 'size'):
      return self.size
    return Int('ptrsize')

  def getPointeeType(self):
    return self.type

  def getUnderlyingType(self):
    return self.type

  def __eq__(self, other):
    if isinstance(other, PtrType):
      return self.type == other.type
    if isinstance(other, UnknownType):
      return other == self
    return BoolVal(False)

  def fixupTypes(self, types):
    self.size = types.evaluate(Int('ptrsize')).as_long()
    self.type.fixupTypes(types)

  def ensureTypeDepth(self, depth):
    return BoolVal(False) if depth == 0 else self.type.ensureTypeDepth(depth-1)

  def getTypeConstraints(self):
    # Pointers are assumed to be either 32 or 64 bits
    v = Int('ptrsize')
    return And(Or(v == 32, v == 64),
               self.typevar == Type.Ptr,
               self.type.getTypeConstraints())


################################
class ArrayType(Type):
  def __init__(self, elems = None, type = None, depth = 0):
    if elems is None:
      assert type is None
      # limit type nesting to 1 level
      if depth >= 0:
        type = IntType()
      else:
        type = UnknownType(depth+1)
      elems = Input('#' + mk_unique_id(), IntType(4)) # enough for [1,7]
    self.elems = TypeFixedValue(elems, 1, 7)
    self.type = type
    assert isinstance(self.type, Type)

  def __repr__(self):
    return '[%s x %s]' % (self.elems, self.type)

  def setName(self, name):
    self.typevar = Int('t_' + name)
    self.type.setName('[' + name + ']')
    self.elems.setName(name, 'elems')

  def __eq__(self, other):
    if isinstance(other, ArrayType):
      return And(self.type == other.type, self.elems == other.elems)
    if isinstance(other, UnknownType):
      return other == self
    return BoolVal(False)

  def getSize(self):
    return self.elems.getValue() * self.type.getSize()

  def getUnderlyingType(self):
    return self.type

  def fixupTypes(self, types):
    self.elems.fixupTypes(types)
    self.type.fixupTypes(types)

  def ensureTypeDepth(self, depth):
    return BoolVal(False) if depth == 0 else self.type.ensureTypeDepth(depth-1)

  def getTypeConstraints(self):
    return And(self.typevar == Type.Array,
               self.elems.getTypeConstraints(),
               self.type.getTypeConstraints())

################################
class UType(object):
  '''Unification types.

  Used to quickly determine which values have the same types as other values.
  If a subset contains any preferred elements, one of those will be selected
  as representative.
  '''
  # TODO: combine this with existing type system?
  # TODO: handle concrete and named types

  def __init__(self, label, preferred=False):
    self._label = label
    self._preferred = preferred
    self._rep = None

  def rep(self):
    if self._rep is self:
      print 'Loop detected for', self._label
      return self
      ## TODO: Change this to assert, or remove

    if self._rep is None:
      return self

    self._rep = self._rep.rep()
    return self._rep

  def label(self):
    return self.rep()._label

  def __eq__(self, other):
    return self.rep() is other.rep()

  def unify(self, other):
    rself = self.rep()
    rother = other.rep()

    if rother is rself:
      return

    if rself._preferred:
      rother._rep = rself
    else:
      rself._rep = rother

def unified_iter(iterable):
  'Unify the arguments and return their representative'
  it = iter(iterable)
  u1 = next(it)
  for u2 in it:
    u1.unify(u2)
  return u1

def unified(*utypes):
  return unified_iter(utypes)

################################
class Value:
  def __deepcopy__(self, m):
    # Disable deep copy.
    return self

  def getName(self):
    return self.name

  def getUniqueName(self):
    return self.name

  @staticmethod
  def _mungeCName(name):
    '''Translate an Alive variable name into a legal C equivalent.
    
    '.' and '_' become 'p_' and 'u_'. Temporaries starting with digits, 'C', or 'V'
    gain a 'V' prefix.
    '''
    s = name.replace('_', 'u_').replace('.', 'p_')
    
    if s[0] == '%':
      s = s[1:]
      if s[0] in '0123456789C':
        s = 'V_' + s

    if s in {'and', 'or', 'not', 'if', 'auto', 'bool'}: #FIXME: add all C++ keywords
      s = 'V_' + s

    return s

  def getCName(self):
    return self._mungeCName(self.getName())
  
  def getLabel(self):
    return self.getCName()

  def toOperand(self):
    return CVariable(self.getCName())

  def toAPIntOrLit(self):
    return self.toAPInt()

  def toCType(self):
    return CVariable(self._manager.rep_for(self.getLabel())).arr('getType',[])

  def isConst(self):
    return False

  def setName(self, name):
    self.name = name
    self.type = copy.deepcopy(self.type)
    self.type.setName(name)
    for attr in dir(self):
      a = getattr(self, attr)
      if isinstance(a, TypeFixedValue):
        a.setName(name, attr)
      elif isinstance(a, Type) and attr != 'type':
        a = copy.deepcopy(a)
        a.setName('%s_%s_%s' % (name, attr, mk_unique_id()))
        setattr(self, attr, a)
      elif isinstance(a, list):
        newa = []
        for e in a:
          if isinstance(e, Type):
            e = copy.deepcopy(e)
            e.setName('%s_%s_%s' % (name, attr, mk_unique_id()))
          newa += [e]
        setattr(self, attr, newa)

  def getTypeConstraints(self):
    c = []
    for attr in dir(self):
      a = getattr(self, attr)
      if isinstance(a, (Type, Value)):
        c += [a.getTypeConstraints()]
      elif isinstance(a, list):
        for e in a:
          if isinstance(e, (Type, Value)):
            c += [e.getTypeConstraints()]
    return mk_and(c)

  def fixupTypes(self, types):
    for attr in dir(self):
      a = getattr(self, attr)
      if isinstance(a, (Type, Value)):
        a.fixupTypes(types)
      elif isinstance(a, list):
        for e in a:
          if isinstance(e, (Type, Value)):
            e.fixupTypes(types)

################################
class TypeFixedValue(Value):
  def __init__(self, v, min, max):
    assert isinstance(v, Value)
    assert isinstance(v.type, IntType)
    self.v = v
    self.min = min
    self.max = max

  def setName(self, name, attr):
    self.name = self.v.getName()
    self.smtvar = Int('val_%s_%s' % (name, attr))

  def getValue(self):
    return getattr(self, 'val', self.smtvar)

  def getType(self):
    return self.v.type

  def __repr__(self):
    return str(self.v)

  def __eq__(self, other):
    assert isinstance(other, TypeFixedValue)
    return self.smtvar == other.smtvar

  def toSMT(self, poison, state, qvars):
    return [], self.val

  def getTypeConstraints(self):
    c = [self.v.getTypeConstraints()]

    if self.v.isConst():
      c += [self.smtvar == self.v.val]
      if not self.v.type.defined:
        c += [self.v.type == self.max.bit_length() + int(self.max >= 0)]
    else:
      if self.v.type.defined:
        mymin = min(self.min, (1 << self.v.type.getSize()) - 1)
        mymax = min(self.max, (1 << self.v.type.getSize()) - 1)
      else:
        mymin = self.min
        mymax = self.max
      c += [self.smtvar >= mymin, self.smtvar <= mymax]
      if not self.v.type.defined:
        c += [self.v.type >= self.max.bit_length() + int(self.max >= 0)]

    return mk_and(c)

  def fixupTypes(self, types):
    self.v.fixupTypes(types)
    self.val = types.evaluate(self.smtvar).as_long()


################################
class Input(Value):
  def __init__(self, name, type):
    self.type = type
    self.setName(name)
    assert isinstance(self.type, Type)

  def __repr__(self):
    return self.getName()

  def toSMT(self, poison, state, qvars):
    ptr = BitVec(self.name, self.type.getSize())
    # if we are dealing with an arbitrary pointer, assume it points to something
    # that can (arbitrarily) hold 7 elements.
    if isinstance(self.type, PtrType):
      block_size = self.type.getSize()
    elif isinstance(self.type, UnknownType) and\
         (self.type.myType == Type.Ptr or self.type.myType == Type.Unknown):
      block_size = self.type.types[Type.Ptr].getSize()
    else:
      return [], ptr

    num_elems = 7
    size = block_size * num_elems
    mem = BitVec('mem_' + self.name, size)
    allOnes = BitVecVal((1 << size) - 1, size)
    state.addAlloca(ptr, mem, (block_size, num_elems, 1, allOnes))
    return [], ptr

  def utype(self):
    return self._utype

  def setRepresentative(self, manager):
    #self._utype = context.repForName(self.getCName())
    self._manager = manager
    manager.add_label(self.getLabel())

  def toAPInt(self):
    name = self.getName()
    if name[0] != 'C':
      raise AliveError('Input {0} used in an expression'.format(name))
    
    return self.toOperand().arr('getValue',[])
