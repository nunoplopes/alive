import argparse, glob, re, sys
from language import *
from precondition import *
from parser import parse_opt_file
from codegen import *

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
      #return 'm_ConstantInt({})'.format(value.val) #TODO specialize m_Zero, m_Ones, etc?
      return CFunctionCall('m_ConstantInt', CVariable(value.val))
    
    name = value.getCName()
    if name in self.seen:
      #return 'm_Specific({})'.format(name)
      return CFunctionCall('m_Specific', CVariable(name))
      
    if not isinstance(value, (Input, Constant)):
      self.todo.append(value)
    
    self.seen.add(name)
    if name[0] == 'C':
      self.addPtr(name, 'ConstantInt')
      #return 'm_ConstantInt({})'.format(name)
      return CFunctionCall('m_ConstantInt', CVariable(name))
    
    self.addPtr(name, 'Value')
    #return 'm_Value({})'.format(name)
    return CFunctionCall('m_Value', CVariable(name))

    
    
  

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

for n,p,s,t,u in opts:
  # transform the last instruction in the source
  context = GenContext()
  
  # find the last instruction in s (skip values declared in the precondition)
  vals = s.values()
  root = vals.pop()
  while not isinstance(root, Instr): 
    root = vals.pop()
  matches = [root.getPatternMatch(context, name = 'I')]

  while context.todo:
    v = context.todo.pop()
    
    matches.append(v.getPatternMatch(context))


  decl_seg = iter_seq(line + decl for decl in context.decls)
  
  if not isinstance(p, TruePred):
    matches.append(p.getPatternMatch())
  
  cond = CIf(CBinExpr.reduce('&&', matches), [])


  code = '{ // ' + n + nest(4, decl_seg + line + line + cond.format()) + line + '}'
  code.pprint()
  
#   for w in (40,50,60,70,80,90,100):
#     code.pprint(w)

#   print '{ //', n
#   for decl in context.decls:
#     print decl
#   
#   print 'if ({0}) {{'.format(' && '.join(matches))
#   print '}'
#   print '}'
  
  
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
