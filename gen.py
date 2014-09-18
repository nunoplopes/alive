import argparse, glob, re, sys
from language import *
from precondition import *
from parser import parse_opt_file
from codegen import *
from itertools import combinations

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

    if isinstance(value, ConstantVal):
      if value.val == 0:
        return CFunctionCall('m_Zero')
      if value.val == 1:
        return CFunctionCall('m_One')
      if value.val == -1:
        return CFunctionCall('m_AllOnes')

      # eventually use m_SpecificInt
      raise AliveError("Can't match literal " + value.val)

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

class UnifyContext(object):
  def __init__(self):
    self.names = {}
    self.sizes = {}
    self.preferred = True

  def newRep(self, size = None):
    if size == None:
      return UType('##ANONYMOUS')

    if not size in self.sizes:
      self.sizes[size] = UType('##i' + str(size))

    return self.sizes[size]

  def repForName(self, name):
    if not name in self.names:
      self.names[name] = UType(name, self.preferred)
    return self.names[name]

  def repForSize(self, size, name):
    if not size in self.sizes:
      self.sizes[size] = UType(name, self.preferred)

    if name in self.names:
      self.sizes[size].unify(self.names[name])
    else:
      self.names[name] = self.sizes[size]

    return self.sizes[size]

    
  

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

print 'bool runOnInstruction(Instruction* I) {'

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

  # make sure the root type is called 'I'
  # TODO: rethink handling of preferences
  ucontext = UnifyContext()
  for v in s.values():
    v.setRepresentative(ucontext)
  ucontext.repForName('I').unify(root.utype())
  ucontext.preferred = False


  # declare variables to be matched in condition
  decl_seg = iter_seq(line + decl for decl in context.decls)
  
  # add non-trivial preconditions
  if not isinstance(p, TruePred):
    p.setRepresentative(ucontext)
    matches.append(p.getPatternMatch())

  # check for type unification implied by target, but not by source
  # for each variable (input?) in both source and target
  both = [k for k in s.iterkeys() if k in t]
  #print 'both=', both
  diff = [(k1,k2) for (k1,k2) in combinations(both, 2) if not s[k1].utype().rep() is s[k2].utype().rep()]
  #print 'diff=', diff

  for k,v in t.iteritems():
    v.setRepresentative(ucontext)
    if k in s:
      if not v.utype().rep() is s[k].utype().rep():
        print 'not unified:', k
        v.utype().unify(s[k].utype())

  need_match = [(k1,k2) for (k1,k2) in diff if t[k1].utype().rep() is t[k2].utype().rep()]
  #print 'need_match=', need_match

  for (k1,k2) in need_match:
    m = CBinExpr('==',
      s[k1].toOperand().arr('getType', []),
      s[k2].toOperand().arr('getType', []))
    # can't use .toCType(), because these are now unified
    matches.append(m)

  gen = [CDefinition(CVariable('Value'), CVariable(v.getCName()), v.toInstruction(), True)
          for (k,v) in t.iteritems() if isinstance(v, Instr) and not k in s]
  new_root = t[root_name]
  gen.append(CDefinition(CVariable('Value'), 
    CVariable(new_root.getCName()), new_root.toInstruction(), True))
  gen.append(CVariable('I').arr('replaceAllUsesWith', [new_root.toOperand()]))
  gen.append(CReturn(CVariable('true')))
  
  cond = CIf(CBinExpr.reduce('&&', matches), gen)


  code = nest(2, line + '{ // ' + n + nest(2, decl_seg + line + line + cond.format()) + line + '}')
  code.pprint()

print
print '  return false;'
print '}'
