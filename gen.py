import argparse, glob, re, sys
from language import *
from precondition import *
from parser import parse_opt_file
from codegen import *
from itertools import combinations, izip, count

HAS_SPECIFIC_INT = True
DO_STATS = True
LIMITER = False
SIMPLIFY = True

class GenContext(object):
  def __init__(self):
    self.seen = set()
    self.todo = []
    self.decls = []
    self.seen_cmps = set()
  
  def addPtr(self, name, ctype):
    self.decls.append(ctype + ' *' + name + ';')
  
  def addVar(self, name, ctype):
    self.decls.append(ctype + ' ' + name + ';')
    # FIXME: don't create duplicate variables
    # FIXME: return CDefinition
    
  def _arg_expr(self, value, bound, extras):
    if isinstance(value, CExpression):
      return value

    if isinstance(value, UndefVal):
      return CFunctionCall('m_Undef')

    if isinstance(value, ConstantVal):
      if value.val == 0:
        return CFunctionCall('m_Zero')
      if value.val == 1:
        return CFunctionCall('m_One')
      if value.val == -1:
        return CFunctionCall('m_AllOnes')

      # eventually use m_SpecificInt
      if HAS_SPECIFIC_INT:
        return CFunctionCall('m_SpecificInt', CVariable(str(value.val)))

      raise AliveError("Can't match literal " + str(value.val))

    # assume value is an instruction or input
    name = value.getCName()
    if name in bound:
      # name has been bound in this match
      old_name = name
      name = name + 'x_' + str(len(self.seen))
      extras.append(CBinExpr('==', CVariable(name), CVariable(old_name)))

    elif name in self.seen:
      # name was bound in a previous call to match
      return CFunctionCall('m_Specific', CVariable(name))

    elif not isinstance(value, (Input, Constant)):
      self.todo.append(value)

    self.seen.add(name)
    bound.add(name)
    if name[0] == 'C':
      self.addPtr(name, 'ConstantInt')
      return CFunctionCall('m_ConstantInt', CVariable(name))
    
    self.addPtr(name, 'Value')
    return CFunctionCall('m_Value', CVariable(name))

  def match(self, varname, matchtype, *args):
    bound = set()
    extras = []

    cargs = [self._arg_expr(arg, bound, extras) for arg in args]
    match = CFunctionCall('match', CVariable(varname), CFunctionCall(matchtype, *cargs))

    return CBinExpr.reduce('&&', [match] + extras)

  def checkNewComparison(self, cmp_name):
    if cmp_name in self.seen_cmps:
      return False

    self.seen_cmps.add(cmp_name)
    return True

class TypeUnifier(object):
  ''' Simple disjoint subset structure.
  
  Maps each type to a representative. Types which have unified have the same
  representative. Also tracks named and explicit types.
  '''
  
  def __init__(self):
    self.reps = {} # invariant: following reps should eventually reach None
    self.names = {}
    self.sizes = {}
    self.preferred = set()
    self.in_source = True

  def add_label(self, label, ty, anon = False):
    if not label in self.reps:
      self.reps[label] = None
      if self.in_source and not anon:
        self.preferred.add(label)

    if isinstance(ty, IntType) and ty.defined:
      if not ty.size in self.sizes:
        self.sizes[ty.size] = set()

      self.sizes[ty.size].add(label)

    if isinstance(ty, NamedType):
      if not ty.name in self.names:
        self.names[ty.name] = set()

      self.names[ty.name].add(label)

  def rep_for(self, label):
    assert label in self.reps
    rep = self.reps[label]
    if rep == None:
      return label

    rep = self.rep_for(rep)
    self.reps[label] = rep
    return rep

  def unify(self, *labels):
    it = iter(labels)
    lab1 = it.next()
    rep1 = self.rep_for(lab1)

    for lab2 in it:
      rep2 = self.rep_for(lab2)
      if rep1 == rep2:
        continue

      if rep2 in self.preferred and not rep1 in self.preferred:
        self.reps[rep1] = rep2
        rep1 = rep2
      else:
        self.reps[rep2] = rep1

  def all_reps(self):
    return [l for l in self.reps if self.reps[l] == None]
  
  def disjoint(self, lab1, lab2):
    return self.rep_for(lab1) != self.rep_for(lab2)

def iter_pairs(iterable):
  it = iter(iterable)
  prev = it.next()
  for next in it:
    yield (prev,next)
    prev = next

def generate_optimization(rule, opt, out):
  n,p,sbb,tbb,s,t,us,ut,tgt_skip = opt
  
  # transform the last instruction in the source
  context = GenContext()
  
  if len(sbb) != 1 or len(tbb) != 1:
    raise AliveError("codegen can't handle multiple-block optimizations: " + n)

  # find the last instruction in s (skip values declared in the precondition)
  vals = s.values()
  root = vals.pop()
  while not isinstance(root, Instr): 
    root = vals.pop()
  matches = [root.getPatternMatch(context, name = 'I')]
  root_name = root.getName()

  while context.todo:
    v = context.todo.pop()
    
    matches.append(v.getPatternMatch(context))

  # declare variables to be matched in condition
  decl_seg = iter_seq(line + decl for decl in context.decls)

  # determine the type constraints implied by the source
  unifier = TypeUnifier()
  for v in s.values():
    v.setRepresentative(unifier)
  
  # make sure the root is labeled I
  unifier.add_label('I', UnknownType())
  unifier.unify('I', root.getLabel())

  # gather types which are not unified by the source or precondition
  p.setRepresentative(unifier)
  disjoint = unifier.all_reps()

  # FIXME: hack to avoid matching pointers
  for r in disjoint:
    if r in unifier.preferred:
      matches.append(CUnaryExpr('!', 
        CFunctionCall('isa<PointerType>', CVariable(r).arr('getType', []))))

  unifier.in_source = False

  # now add type equalities implied by the target
  for k,v in t.iteritems():
    v.setRepresentative(unifier)

  # check each pairing of types disjoint in the source to see if they have unified
  # NOTE: a set of n disjoint sets that all unify will produce n(n-1)/2 checks,
  #       but only n-1 are required. This is unlikely to be a problem in practice
  for (l1,l2) in combinations(disjoint, 2):
    if not unifier.disjoint(l1,l2):
      m = CBinExpr('==',
        CVariable(l1).arr('getType', []),
        CVariable(l2).arr('getType', []))
      matches.append(m)

  for sz in unifier.sizes:
    # gather reps for this size's types
    reps = {unifier.rep_for(l) for l in unifier.sizes[sz]}
    for rep in reps:
      if not rep in unifier.preferred:
        continue
        # NOTE: this will miss weird cases such as a constant expression with an 
        #       explicit type that isn't used anywhere else (eg. zext i4 0)

      m = CBinExpr('==',
        CVariable(rep).arr('getType', []).arr('getScalarSizeInBits', []),
        CVariable(str(sz)))
      matches.append(m)

    unifier.unify(*reps)

  for nm in unifier.names:
    # gather reps for this name
    reps = {unifier.rep_for(l) for l in unifier.names[nm]}
    for (r1,r2) in iter_pairs(reps):
      m = CBinExpr('==',
        CVariable(r1).arr('getType', []),
        CVariable(r2).arr('getType', []))
      matches.append(m)

    unifier.unify(*reps)

  #assert all(rep in unifier.preferred for rep in unifier.all_reps())

  #non_preferred = [rep for rep in unifier.all_reps() if not rep in unifier.preferred]
  #if non_preferred:
  #  print >> sys.stderr, 'WARNING: Non-preferred reps in <{0}>: {1}'.format(n, non_preferred)

  # add non-trivial preconditions
  if not isinstance(p, TruePred):
    matches.append(p.getPatternMatch())

  # prevent infinite loops (for debugging)
  if DO_STATS and LIMITER:
    matches.append(CBinExpr('<', CVariable('Rule' + str(rule)), CVariable('10000')))

  gen = []
  if DO_STATS:
    gen.append(CUnaryExpr('++', CVariable('Rule' + str(rule))))

  for (k,v) in t.iteritems():
    if isinstance(v, Instr) and k not in tgt_skip and k != root_name:
      if isinstance(v, CopyOperand):
        gen.append(CDefinition(CVariable('Value'), 
          CVariable(v.getCName()), v.toInstruction(), True))
      else:
        gen.extend(v.toConstruct())
        #gen.append(CVariable('Worklist').dot('Add', [v.toOperand()]))

  new_root = t[root_name]
  if isinstance(new_root, CopyOperand):
    gen.append(CDefinition(CVariable('Instruction'),
      new_root.toOperand(),
      CFunctionCall('ReplaceInstUsesWith', CVariable('*I'), new_root.toInstruction()), True))
  else:
    gen.extend(new_root.toConstruct(is_root = True))
  gen.append(CReturn(new_root.toOperand()))

  
  cond = CIf(CBinExpr.reduce('&&', matches), gen)


  code = nest(2, line + '{ // ' + n + nest(2, decl_seg + line + line + cond.format()) + line + '}')
  out.write(code.format())

def generate_suite(opts, out):
  "Generate code for a list of transformations"

  opts = list(izip(count(1), opts))

  # gather names of testcases
  if DO_STATS:
    for rule, opt in opts:
      name = opt[0]
      # TODO: abstract this
      src_vals = opt[4].values()
      root = src_vals.pop()
      while not isinstance(root, Instr):
        root = src_vals.pop()

      #FIXME: sanitize name
      out.write('STATISTIC(Rule{0}, "{0}. {1} {2}");\n'.format(rule, root.getOpName(), name))

  out.write('Instruction *InstCombiner::runOnInstruction(Instruction *I) {\n')

  if SIMPLIFY:
    out.write('''
  if (Value *V = SimplifyInstruction(I, DL, TLI, DT, AT)) {
    return ReplaceInstUsesWith(*I, V);
  }
''')


  for rule, opt in opts:
    generate_optimization(rule, opt, out)

  out.write('''

  return nullptr;
}
''')


if __name__ == '__main__':
  opts = parse_opt_file(sys.stdin.read())
  generate_suite(opts, sys.stdout)
