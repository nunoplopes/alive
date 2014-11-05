import argparse, glob, re, sys
from language import *
from precondition import *
from parser import parse_opt_file
from codegen import *
from itertools import combinations

HAS_SPECIFIC_INT = False
DO_STATS = True

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
    #self.names = {}
    #self.sizes = {}
    self.preferred = set()
    self.in_source = True

  def add_label(self, label, anon = False):
    if not label in self.reps:
      self.reps[label] = None
      if self.in_source and not anon:
        self.preferred.add(label)

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

# class UnifyContext(object):
#   def __init__(self):
#     self.names = {}
#     self.sizes = {}
#     self.preferred = True
# 
#   def newRep(self, size = None):
#     if size == None:
#       return UType('##ANONYMOUS')
# 
#     if not size in self.sizes:
#       self.sizes[size] = UType('##i' + str(size))
# 
#     return self.sizes[size]
# 
#   def repForName(self, name):
#     if not name in self.names:
#       self.names[name] = UType(name, self.preferred)
#     return self.names[name]
# 
#   def repForSize(self, size, name):
#     if not size in self.sizes:
#       self.sizes[size] = UType(name, self.preferred)
# 
#     if name in self.names:
#       self.sizes[size].unify(self.names[name])
#     else:
#       self.names[name] = self.sizes[size]
# 
#     return self.sizes[size]
# 

test = '''
%C = icmp eq %X, %Y
%11 = select %C, %C, %V
%1 = zext %11
%0 = add %b.c_d, %1
%r = add %0, C2
=>
%r = add %b.c_d,  C2
'''

#opts = parse_opt_file(open('tests/instcombine/andorxor.opt').read())
#opts = parse_opt_file(test)
opts = parse_opt_file(sys.stdin.read())

# gather names of testcases
if DO_STATS:
  rule = 1
  for opt in opts:
    n = opt[0]
    #FIXME: sanitize name
    print 'STATISTIC(Rule{0}, "{0}. {1}");'.format(rule, n)
    rule += 1

print 'bool runOnInstruction(Instruction* I) {'

rule = 1
for n,p,s,t,us,ut in opts:
  # transform the last instruction in the source
  context = GenContext()
  
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
  unifier.add_label('I')
  unifier.unify('I', root.getLabel())
  
  unifier.is_source = False
  
  # add non-trivial preconditions
  if not isinstance(p, TruePred):
    p.setRepresentative(unifier)
    matches.append(p.getPatternMatch())

  # gather types which are not unified by the source
  disjoint = unifier.all_reps()

  # check for type unification implied by target, but not by source
  # for each variable (input?) in both source and target
#   both = [k for k in s.iterkeys() if k in t]
#   print 'both=', both
#   diff = [(k1,k2) for (k1,k2) in combinations(both, 2) if unifier.disjoint(s[k1].getLabel(), s[k2].getLabel())]
#   print 'diff=', diff

  # now add type equalities implied by the target
  for k,v in t.iteritems():
    v.setRepresentative(unifier)
#       if not v.utype().rep() is s[k].utype().rep():
#         print 'not unified:', k
#         v.utype().unify(s[k].utype())

  # check each pairing of types disjoint in the source to see if they have unified
  for (l1,l2) in combinations(disjoint, 2):
    if not unifier.disjoint(l1,l2):
      m = CBinExpr('==',
        CVariable(l1).arr('getType', []),
        CVariable(l2).arr('getType', []))
      matches.append(m)

#   need_match = [(k1,k2) for (k1,k2) in diff if t[k1].utype().rep() is t[k2].utype().rep()]
#   print 'need_match=', need_match
# 
#   for (k1,k2) in need_match:
#     m = CBinExpr('==',
#       s[k1].toOperand().arr('getType', []),
#       s[k2].toOperand().arr('getType', []))
#     # can't use .toCType(), because these are now unified
#     matches.append(m)

  gen = []
  if DO_STATS:
    gen.append(CUnaryExpr('++', CVariable('Rule' + str(rule))))

  for (k,v) in t.iteritems():
    if isinstance(v, Instr) and not k in s:
      gen.extend(v.toConstruct())
  new_root = t[root_name]
  gen.extend(new_root.toConstruct())
  gen.append(CVariable('I').arr('replaceAllUsesWith', [new_root.toOperand()]))
  gen.append(CReturn(CVariable('true')))

  
  cond = CIf(CBinExpr.reduce('&&', matches), gen)


  code = nest(2, line + '{ // ' + n + nest(2, decl_seg + line + line + cond.format()) + line + '}')
  code.pprint()
  rule += 1

print
print '  return false;'
print '}'
