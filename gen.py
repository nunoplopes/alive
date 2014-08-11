import argparse, glob, re, sys
from language import *
from parser import parse_opt_file

class GenContext(object):
  def __init__(self):
    self.seen = set()
    self.todo = []
    self.decls = []
  
  def addPtr(self, name, ctype):
    self.decls.append(ctype + ' *' + name + ';')
  
  def addVar(self, name, ctype):
    self.decls.append(ctype + ' ' + name + ';')
  
  def ref(self, value):
    'Returns an expression matching the given value.'
    
    if isinstance(value, ConstantVal):
      return 'm_ConstantInt({})'.format(value.val) #TODO specialize m_Zero, m_Ones, etc?
    
    name = value.getCName()
    if name in self.seen:
      return 'm_Specific({})'.format(name)
      
    if not isinstance(value, (Input, Constant)):
      self.todo.append(value)
    
    self.seen.add(name)
    if name[0] == 'C':
      self.addPtr(name, 'ConstantInt')
      return 'm_ConstantInt({})'.format(name)
    
    self.addPtr(name, 'Value')
    return 'm_Value({})'.format(name)

    
    
  

test = '''
%1 = select %C, %C, %V
%0 = add %b.c_d, C1
%r = add %0, C2
=>
%r = add %b.c_d, C1 + C2
'''

#opts = parse_opt_file(open('tests/instcombine/andorxor.opt').read())
#opts = parse_opt_file(test)
opts = parse_opt_file(sys.stdin.read())

for n,p,s,t in opts:
  # transform the last instruction in the source
  context = GenContext()
  matches = [s.values()[-1].getPatternMatch(context, name = 'I')]
  while context.todo:
    v = context.todo[0]
    context.todo = context.todo[1:]
    
    matches.append(v.getPatternMatch(context))
  
  print '{ //', n
  for decl in context.decls:
    print decl
  
  print 'if ({0}) {{'.format(' && '.join(matches))
  print '}'
  print '}'
  
  
#   # declarations
#   for v in s.itervalues():
#     # don't declare constants
#     if isinstance(v, Constant):
#       continue
#     
#     name = v.getCName()
#     # v is a constant iff its name starts with C
#     if name[0] == 'C':
#       print 'ConstantInt *{0};'.format(name)
#     else:
#       print 'Value *{0};'.format(name)
#   
#   context = GenContext()
#   
#   # get matches
#   vals = [v for v in s.itervalues() if (not isinstance(v, (Constant,Input)))]
#   vals.reverse()
#   for v in vals:
#     
#     print v.getPatternMatch(context)
#     
