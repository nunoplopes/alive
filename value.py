# Copyright 2014-2015 The Alive authors.
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

def mkTyEqual(types):
  return [types[0] == types[i] for i in range(1, len(types))]

def create_mem_if_needed(ptr, val, state, qvars):
    # if we are dealing with an arbitrary pointer, assume it points to something
    # that can (arbitrarily) hold 7 elements.
    if isinstance(val.type, PtrType):
      block_size = val.type.getSize()
    elif isinstance(val.type, UnknownType) and val.type.myType == Type.Ptr:
      block_size = val.type.types[Type.Ptr].getSize()
    else:
      return

    num_elems = 7
    size = block_size * num_elems
    state.addInputMem(ptr, qvars, block_size, num_elems)


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
    self.myType = types.get_interp(self.typevar).as_long()
    self.types[self.myType].fixupTypes(types)

  def __eq__(self, other):
    if self.myType != self.Unknown:
      return And(self.typevar == self.myType,
                 self.types[self.myType] == other)

    for i,type in self.types.iteritems():
      if isinstance(other, type.__class__):
        self.myType = i
        return And(self.typevar == i, type == other)

    c = []
    if isinstance(other, UnknownType):
      for i,type in self.types.iteritems():
        if other.types.has_key(i):
          c += [And(self.typevar == i,
                    other.typevar == i,
                    type == other.types[i])]
    else:
      for i,type in self.types.iteritems():
        c += [And(self.typevar == i, type == other)]
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
    size = types.get_interp(self.bitsvar).as_long()
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
    c = [self.typevar == Type.Int]
    if self.defined:
      c += [self.bitsvar == self.getSize()]
    else:
      # Integers are assumed to be up to 64 bits.
      # We bias towards 4/8 bits, as counterexamples become easier to understand
      c += [Or(self.bitsvar == 8, self.bitsvar == 4,
               And(self.bitsvar > 0, self.bitsvar <= 64))]
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
    self.size = get_ptr_size()
    self.type.fixupTypes(types)

  def ensureTypeDepth(self, depth):
    return BoolVal(False) if depth == 0 else self.type.ensureTypeDepth(depth-1)

  def getTypeConstraints(self):
    return And(self.typevar == Type.Ptr,
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
class Value:
  def __deepcopy__(self, m):
    # Disable deep copy.
    return self

  def getName(self):
    return self.name

  def getUniqueName(self):
    return self.name

  def isConst(self):
    return False

  def setName(self, name):
    self.name = name
    if hasattr(self, 'type'):
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

  def countUsers(self, m):
    for attr in dir(self):
      a = getattr(self, attr)
      if isinstance(a, Value):
        name = a.getUniqueName()
        m[name] = m.get(name, 0) + 1


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

  def toSMT(self, defined, state, qvars):
    return self.val, BoolVal(True)

  def getTypeConstraints(self):
    c = [self.v.getTypeConstraints()]

    if self.v.isConst():
      c += [self.smtvar == self.v.val]
      if not self.v.type.defined:
        c += [self.v.type == self.max.bit_length()]
    else:
      if self.v.type.defined:
        mymin = min(self.min, (1 << self.v.type.getSize()) - 1)
        mymax = min(self.max, (1 << self.v.type.getSize()) - 1)
      else:
        mymin = self.min
        mymax = self.max
      c += [self.smtvar >= mymin, self.smtvar <= mymax]
      if not self.v.type.defined:
        c += [self.v.type >= self.max.bit_length()]

    return mk_and(c)

  def fixupTypes(self, types):
    self.v.fixupTypes(types)
    self.val = types.get_interp(self.smtvar).as_long()


################################
class Input(Value):
  def __init__(self, name, type):
    self.type = type
    self.setName(name)
    assert isinstance(self.type, Type)

  def __repr__(self):
    return self.getName()

  def toSMT(self, defined, state, qvars):
    v = BitVec(self.name, self.type.getSize())
    create_mem_if_needed(v, self, state, [])
    if self.name[0] == 'C':
      return v, BoolVal(True)
    uv = BitVec('def_' + self.name, 1)
    return v, uv == 1

  def register_types(self, manager):
    if self.name[0] == 'C':
      min = IntType()
    else:
      min = UnknownType()

    manager.register_type(self, self.type, min)

  def _ensure_constant(self):
    name = self.getName()
    if name[0] != 'C':
      raise AliveError('Input {0} used in an expression'.format(name))

  def get_APInt_or_u64(self, manager):
    return self.get_APInt(manager)

  def get_APInt(self, manager):
    self._ensure_constant()
    return manager.get_cexp(self).arr('getValue', [])

  def get_Value(self, manager):
    assert False
    # this should have been called through the manager
