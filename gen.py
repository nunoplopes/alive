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



import argparse, glob, re, sys
from language import *
from precondition import *
from parser import parse_opt_file
from codegen import *
from itertools import combinations, count
from collections import defaultdict
import six
from six.moves import zip
from six.moves import range

DO_STATS = True
SIMPLIFY = True
LIMITER = False

def get_most_specific_type(t1, t2):
  def _mismatch(c):
    if c:
      raise AliveError('Incomparable types: {0}, {1}'.format(type_str(t1), type_str(t2)))

  if isinstance(t1, UnknownType):
    try:
      if isinstance(t2, IntType):
        return get_most_specific_type(t1.types[Type.Int], t2)
      if isinstance(t2, PtrType):
        return get_most_specific_type(t1.types[Type.Ptr], t2)
      if isinstance(t2, ArrayType):
        return get_most_specific_type(t1.types[Type.Array], t2)
    except KeyError:
      _mismatch(True)

    # TODO: return t1 or t2 when possible?
    types = [(s, get_most_specific_type(t, t2.types[s]))
      for (s,t) in six.iteritems(t1.types) if s in t2.types]

    _mismatch(not types)

    if len(types) == 1:
      return types[0][1]

    t3 = UnknownType()
    t3.types = dict(types)
    return t3

  if isinstance(t2, UnknownType):
    return get_most_specific_type(t2,t1)

  _mismatch(t1.__class__ != t2.__class__)
  if isinstance(t1, IntType):
    _mismatch(t1.defined and t2.defined and
                         t1.getSize() != t2.getSize())
    return t1 if t1.defined else t2

  if isinstance(t1, PtrType):
    # TODO: return t1 or t2 when possible?
    return PtrType(get_most_specific_type(t1.type, t2.type))

  if isinstance(t1, ArrayType):
    #sys.stderr.write('WARNING: get_most_specific_type of ArrayTypes\n')
    return t1 # FIXME

  #TODO: array types?
  _mismatch(True)


class CodeGenerator(object):
  Source, Target = list(range(2))

  PtrConstantInt = CPtrType(CTypeName('ConstantInt'))
  PtrValue = CPtrType(CTypeName('Value'))
  PtrInstruction = CPtrType(CTypeName('Instruction'))

  def __init__(self):
    self.fresh = 0
    self.value_names = {} # value -> name
    self.key_names = {}   # key -> name
    self.names = set()    # all created names
    self.name_type = {}   # name -> ctype
    self.reps = {}        # value -> value
    self.required = {}    # value -> type
    self.guaranteed = {}  # value -> type
    self.named_types = defaultdict(set)
    self.phase = CodeGenerator.Source
    self.clauses = []

  def dump(self, title):
    from pprint import pprint
    def lookup(v):
      if v == None: return None
      return self.value_names.get(v, '<' + v.getUniqueName() + '>')

    print('----', title)
    print('value_names:', end=' ')
    pprint(set([(v.getUniqueName(),n) for v,n in six.iteritems(self.value_names)]))
    print('key_names:', end=' ')
    pprint(self.key_names)
    print('names:', end=' ')
    pprint(self.names)
    print('bound: ', end=' ')
    pprint(dict([(n,str(t)) for (n,t) in six.iteritems(self.name_type)]))
    print('reps:', end=' ')
    pprint(dict([(lookup(v), lookup(r)) for (v,r) in six.iteritems(self.reps)]))
    print('required:', end=' ')
    pprint(dict([(lookup(v), type_str(t)) for v,t in six.iteritems(self.required)]))
    print('guaranteed:', end=' ')
    pprint(dict([(lookup(v), type_str(t)) for v,t in six.iteritems(self.guaranteed)]))
    print('named_types:', end=' ')
    pprint(self.named_types)
    print('----')

  def get_name(self, value):
    'Return the name for this value, creating one if needed'

    assert isinstance(value, (Input, Instr))

    if value in self.value_names:
      return self.value_names[value]

    name = self.new_name(value.getName())
    self.value_names[value] = name

    return name

  def get_key_name(self, key):
    'Return the name for this key, creating one if needed'

    if key in self.key_names:
      return self.key_names[key]

    name = self.new_name(key)
    self.key_names[key] = name

    return name

  def bound(self, var):
    'Returns whether the name or value is currently bound'

    if isinstance(var, Value):
      return var in self.value_names and \
        self.value_names[var] in self.name_type

    return var in self.name_type

  def get_cexp(self, var):
    'Return a CExp referring to this name or value'

    if isinstance(var, Constant):
      return var.get_Value(self)

    if isinstance(var, Value):
      var = self.get_name(var)

    #assert var in self.name_type

    return CVariable(var)

  def get_rep(self, value):
    "Return the representative for this value's type"

    if value not in self.reps:
      self.reps[value] = None
      return value

    if self.reps[value] == None:
      return value

    rep = self.get_rep(self.reps[value])
    self.reps[value] = rep

    return rep


  def get_llvm_type(self, value):
    "Return a CExpression giving the value's LLVM type"

    rep = self.get_rep(value)
    assert(self.bound(rep))
    return self.get_cexp(rep).arr('getType', [])


  def get_ctype(self, name):
    "Return this name's type as a CType"

    return self.name_type[name]

  keywords = {'alignas', 'alignof', 'and', 'and_eq',
    'asm', 'auto', 'bitand', 'bitor', 'bool', 'break',
    'case', 'catch', 'char', 'char16_t', 'char32_t',
    'class', 'compl', 'const', 'constexpr', 'const_cast',
    'continue', 'decltype', 'default', 'delete', 'do',
    'double', 'dynamic_cast', 'else', 'enum', 'explicit',
    'export', 'extern', 'false', 'float', 'for', 'friend',
    'goto', 'if', 'inline', 'int', 'long', 'mutable',
    'namespace', 'new', 'noexcept', 'not', 'not_eq',
    'nullptr', 'operator', 'or', 'or_eq', 'private',
    'protected', 'public', 'register', 'reinterpret_cast',
    'return', 'short', 'signed', 'sizeof', 'static',
    'static_assert', 'static_cast', 'struct', 'switch',
    'template', 'this', 'thread_local', 'throw', 'true',
    'try', 'typedef', 'typeid', 'typename', 'union',
    'unsigned', 'using', 'virtual', 'void', 'volatile',
    'wchar_t', 'while', 'xor', 'xor_eq'}
    #TODO: add variables/macros known to be in scope?

  def new_name(self, hint=None):
    "Return a fresh name, related to the hint if given"

    if hint:
      # remove non-ident characters
      hint = re.sub('[^a-zA-Z0-9_]', '', hint)

      # remove double underscores and initial and final underscores
      hint = re.sub('__+', '_', hint)
      hint = re.sub('^_|_$', '', hint)

    if not hint:
      hint = 'V'
    elif hint[0].isdigit() or hint in self.keywords:
      hint = '_' + hint

    name = hint
    while name in self.names:
      name = hint + '_' + str(self.fresh)
      self.fresh += 1

    self.names.add(name)
    return name

  @staticmethod
  def value_ctype(value):
    if isinstance(value, Input) and value.name[0] == 'C':
      return CodeGenerator.PtrConstantInt

    return CodeGenerator.PtrValue

  def bind_value(self, value):
    "Add this value to the set of bound names"
    assert isinstance(value, (Input, Instr))

    ctype = self.value_ctype(value)
    name = self.get_name(value)
    self.bind_name(name, ctype)

  def bind_name(self, name, ctype):
    "Add this name to the set of bound names"

    assert name not in self.name_type
    assert isinstance(name, str)

    if name not in self.names:
      name = self.new_name(name)

    self.name_type[name] = ctype

  def register_type(self, value, actual, minimal):
    "Set the LLVM type constraints for this value"

    rep = self.get_rep(value)

    if isinstance(actual, NamedType):
      self.named_types[actual.name].add(rep)
      actual = actual.type

    if isinstance(minimal, NamedType):
      minimal = minimal.type # should never happen

    # ensure that the actual type is at least as specific as the minimal type
    actual = get_most_specific_type(actual, minimal)

    if rep in self.required:
      self.required[rep] = get_most_specific_type(actual, self.required[rep])
    else:
      self.required[rep] = actual

    if self.phase == self.Source:
      if rep in self.guaranteed:
        self.guaranteed[rep] = get_most_specific_type(minimal, self.guaranteed[rep])
      else:
        self.guaranteed[rep] = minimal

  def unify(self, *values):
    "Constrain the given values to have the same LLVM type"

    it = iter(values)
    v1 = next(it)
    r1 = self.get_rep(v1)

    for v2 in it:
      r2 = self.get_rep(v2)
      if r1 is r2:
        continue

      if self.phase != self.Source and self.bound(r1) and self.bound(r2):
        self.clauses.append(
          CBinExpr('==', self.get_llvm_type(r1), self.get_llvm_type(r2)))

      if self.bound(r2) and not self.bound(r1):
        r1, r2 = r2, r1

      self.reps[r2] = r1

      if r2 in self.required:
        self.required[r1] = get_most_specific_type(self.required[r1], self.required[r2])
        del self.required[r2]

      if r2 in self.guaranteed:
        self.guaranteed[r1] = get_most_specific_type(self.guaranteed[r1], self.guaranteed[r2])
        del self.guaranteed[r2]


class MatchBuilder(object):
  CTypeName = CTypeName

  def __init__(self, manager, value):
    self.manager = manager
    self.value = value
    self.bound = []
    self.extras = []

  def get_my_ref(self):
    return self.manager.get_cexp(self.value)

  def new_name(self, hint=None):
    'Create a fresh name'
    return self.manager.new_name(hint)

  def simple_match(self, matcher, *subpatterns):
    return CFunctionCall('match',
      self.get_my_ref(),
      CFunctionCall(matcher, *subpatterns))

  def binding(self, name, ctype):
    '''Bind this variable, returning a CExpr subpattern.

    NOTE: If the name is already bound, this will return a fresh name
    and add a requirement that the new name equal the old one.
    '''

    if self.manager.bound(name):
      # create a new name and bind it
      new_name = self.manager.new_name(name)

      # add the equality constraint
      self.extras.append(CBinExpr('==', CVariable(new_name), CVariable(name)))

      #TODO: check that the types are equal

      name = new_name

    self.manager.bind_name(name, ctype)
    return CVariable(name)


  def subpattern(self, value):
    'Return a CExpr which matches the operand value and binds its variable'

    if isinstance(value, ConstantVal):
      self.bound.append(value)
      return CFunctionCall('m_SpecificInt', CVariable(str(value.val)))
      # NOTE: using m_Zero is unadvisable here, because it matches null

    assert isinstance(value, (Instr, Input))

    if value not in self.bound:
      if self.manager.bound(value):
        return CFunctionCall('m_Specific', self.manager.get_cexp(value))

      self.bound.append(value)
      self.manager.bind_value(value)
      name = self.manager.get_name(value)

    else:
      # create a new value and require it equal the old one
      name = self.manager.new_name(value.getName())
      self.manager.bind_name(name, self.manager.value_ctype(value))
      self.extras.append(CBinExpr('==', self.manager.get_cexp(value), CVariable(name)))

    # TODO: better to look up the ctype?
    if value.name[0] == 'C':
      return CFunctionCall('m_ConstantInt', CVariable(name))

    return CFunctionCall('m_Value', CVariable(name))


def type_str(atype):
  if isinstance(atype, IntType):
    if atype.defined:
      return 'i' + str(atype.size)
    return 'iN'

  if isinstance(atype, PtrType):
    return type_str(atype.type) + '*'

  if isinstance(atype, ArrayType):
    return type_str(atype.type) + '[]'

  if isinstance(atype, UnknownType):
    return '(' + '|'.join(type_str(t) for t in list(atype.types.values())) + ')'

  return '?'

def get_root(src):
  values = list(src.values())
  root = values.pop()
  while not isinstance(root, Instr):
    root = values.pop()

  return root


def match_value(value, manager):
  mb = MatchBuilder(manager, value)
  exp = value.visit_source(mb)

  if mb.extras:
    exp = CBinExpr('&&', exp, CBinExpr.reduce('&&', mb.extras))

  return exp, mb.bound


def minimal_type_constraints(ty_exp, required, guaranteed):
  # TODO: simplify this
  if isinstance(required, IntType):
    if not isinstance(guaranteed, IntType):
      if required.defined:
        return [CFunctionCall('isa<IntegerType>', ty_exp),
          CBinExpr('==',
            ty_exp.arr('getScalarSizeInBits', []),
            CVariable(str(required.size)))]

      return [CFunctionCall('isa<IntegerType>', ty_exp)]

    if required.defined and not guaranteed.defined:
      return [CBinExpr('==',
        ty_exp.arr('getScalarSizeInBits', []),
        CVariable(str(required.size)))]

    return []

  if isinstance(required, PtrType):
    if not isinstance(guaranteed, PtrType):
      raise AliveError("Pointer types not supported")

    return []

  if isinstance(required, ArrayType):
    raise AliveError("Array types not supported")

  assert(isinstance(required, UnknownType))

  reqs = list(required.types.keys())
  reqs.sort()

  guars = list(guaranteed.types.keys())
  guars.sort()

  if reqs == [Type.Int, Type.Ptr] and Type.Array in guars:
    return [CVariable('<int-or-ptr>')]

  return []
  #FIXME: should handle all types

def generate_opt(rule, opt, out):
  #TODO: break into smaller pieces
  #TODO: handle multiple replacement patterns
  name, pre, src_bb, tgt_bb, src, tgt, src_used, tgt_used, tgt_skip = opt

  if len(src_bb) != 1 or len(tgt_bb) != 1:
    raise AliveError("codegen can't handle multiple basic blocks: " + name)

  root = get_root(src)

  cg = CodeGenerator()
  cg.value_names[root] = 'I'
  cg.bind_value(root)

  todo = [root]
  clauses = []

  while todo:
    val = todo.pop()
    if isinstance(val, Instr):
      exp, new_vals = match_value(val, cg)
      clauses.append(exp)
      todo.extend(reversed(new_vals))

    val.register_types(cg)

  cg.phase = cg.Target

  pre.register_types(cg)

  # ensure named types are unified
  for name in cg.named_types:
    cg.unify(*cg.named_types[name])


  tgt_vals = [v for k,v in six.iteritems(tgt) if not (isinstance(v,Input) or k in tgt_skip)]

  for value in tgt_vals:
    value.register_types(cg)

  root_name = root.getName()
  new_root = tgt[root_name]
  cg.unify(root, new_root)
  clauses.extend(cg.clauses)

  for v,t in six.iteritems(cg.guaranteed):
    if not cg.bound(v): continue

    clauses.extend(minimal_type_constraints(cg.get_llvm_type(v), cg.required[v], t))

  if not isinstance(pre, TruePred):
    clauses.append(pre.visit_pre(cg))

  if DO_STATS and LIMITER:
    clauses.append(CBinExpr('<', CVariable('Rule' + str(rule)), CVariable('10000')))

  body = []

  if DO_STATS:
    body = [CUnaryExpr('++', CVariable('Rule' + str(rule)))]

  for value in tgt_vals:
    if isinstance(value, Instr) and value != new_root:
      body.extend(value.visit_target(cg, True))


  if isinstance(new_root, CopyOperand):
    body.append(
      CDefinition.init(
        cg.PtrInstruction,
        cg.get_cexp(tgt[root_name]),
        CFunctionCall('replaceInstUsesWith', CVariable('*I'), cg.get_cexp(new_root.v))))
  else:
    body.extend(new_root.visit_target(cg, False))

  body.append(CReturn(cg.get_cexp(new_root)))

  cif = CIf(CBinExpr.reduce('&&', clauses), body).format()

  decl_it = CDefinition.block((t, CVariable(v))
    for v,t in six.iteritems(cg.name_type) if v != 'I')
  decl = iter_seq(line + d.format() for d in decl_it)

  code = nest(2,
    seq(line, '{ // ', name,
        nest(2, seq(decl, line, line, cif)), line, '}'))

  out.write(code.format())



def generate_suite(opts, out):
  opts = list(zip(count(1), opts))

  # gather names of testcases
  if DO_STATS:
    for rule, opt in opts:
      name = opt[0]
      # TODO: abstract this
      src_root = get_root(opt[4]).getOpName()

      # FIXME: sanitize name
      out.write('STATISTIC(Rule{0}, "{0}. {1} {2}");\n'.format(rule, src_root, name))

    out.write('\n')

  out.write('Instruction *InstCombiner::runOnInstruction(Instruction *I) {\n')

  if SIMPLIFY:
    out.write('''
  if (Value *V = SimplifyInstruction(I, SQ)) {
    return replaceInstUsesWith(*I, V);
  }
''')

  for rule, opt in opts:
    generate_opt(rule, opt, out)

  out.write('\n\n  return nullptr;\n}\n')

llvm_opcode = {
  'add': 'Instruction::Add',
  'sub': 'Instruction::Sub',
  'mul': 'Instruction::Mul',
  'sdiv': 'Instruction::SDiv',
  'srem': 'Instruction::SRem',
  'udiv': 'Instruction::UDiv',
  'urem': 'Instruction::URem',
  'shl':  'Instruction::Shl',
  'lshr': 'Instruction::LShr',
  'ashr': 'Instruction::AShr',
  'and':  'Instruction::And',
  'or':   'Instruction::Or',
  'xor':  'Instruction::Xor',
  'sext': 'Instruction::SExt',
  'zext': 'Instruction::ZExt',
  'trunc': 'Instruction::Trunc',
  'ptrtoint': 'Instruction::PtrToInt',
  'inttoptr': 'Instruction::IntToPtr',
  'bitcast': 'Instruction::BitCast',
  'icmp': 'Instruction::ICmp',
  'select': 'Instruction::Select',
}

def generate_switched_suite(opts, out):
  root_opts = defaultdict(list)
  opts = list(zip(count(1), opts))

  # gather names of testcases
  if DO_STATS:
    for rule, opt in opts:
      name = opt[0]
      # TODO: abstract this
      src_root = get_root(opt[4]).getOpName()

      # FIXME: sanitize name
      out.write('STATISTIC(Rule{0}, "{1}.{0}. {2}");\n'.format(rule, src_root, name))

  out.write('Instruction *InstCombiner::runOnInstruction(Instruction *I) {\n')

  if SIMPLIFY:
    out.write('''
  if (Value *V = SimplifyInstruction(I, SQ)) {
    return replaceInstUsesWith(*I, V);
  }
''')

  out.write('  switch (I->getOpcode()) {\n  default: break;\n')

  # sort opts by root opcode
  for opt in opts:
    root_opts[get_root(opt[1][4]).getOpName()].append(opt)

  for root, opts in six.iteritems(root_opts):
    if root not in llvm_opcode:
      continue

    out.write('  case {0}:\n'.format(llvm_opcode[root]))

    for rule, opt in opts:
      generate_opt(rule, opt, out)

    out.write('\n  break;\n\n')

  out.write('''
  }

  return nullptr;
}
''')



if __name__ == '__main__':
  input = sys.stdin.read()
  generate_switched_suite(parse_opt_file(input), sys.stdout)
