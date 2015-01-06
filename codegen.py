from pretty import *
from collections import defaultdict

class CFragment(object):
	'Common superclass for C statements and expressions.'

  INDENT=2

class CTest(CFragment):
	def __init__(self, string):
		self.s = string
	
	def format(self):
		return text(self.s + ';')
	
	def formatExpr(self, prec):
		return text(self.s)

class CType(CFragment):
  pass

class CPtrType(CType):
  def __init__(self, pointee):
    self.pointee = pointee

  def __str__(self):
    return str(self.pointee) + '*'

  def __repr__(self):
    return 'CPtrType({0.pointee!r})'.format(self)

  def decorate(self, exp):
    return CUnaryExpr('*', self.pointee.decorate(exp))

  def underlying_type(self):
    return self.pointee.underlying_type()

  def format(self):
    return self.pointee.format() + '*'

class CTypeName(CType):
  def __init__(self, name):
    self.name = name

  def __str__(self):
    return self.name

  def __repr__(self):
    return 'CTypeName({0.name!r})'.format(self)

  def decorate(self, exp):
    return exp

  def underlying_type(self):
    return self.name

  def format(self):
    return text(self.name)


class CExpression(CFragment):
	def pprint(self, width=80, prec=0):
		self.formatExpr(prec).pprint(width)

	def dot(self, field, args=None):
		return CFieldAccess(self, field, args)

	def arr(self, field, args=None):
		return CFieldAccess(self, field, args, direct=False)

	def format(self):
		return self.formatExpr(18) + ';'

class CVariable(CExpression):
	def __init__(self, name):
		self.name = name
	
	def formatExpr(self, prec=0):
		return text(self.name)

class CFunctionCall(CExpression):
	def __init__(self, fun, *args):
		self.fun = fun
		self.args = args
	
	def formatExpr(self, prec = 0):
		if len(self.args) == 0:
			return text(self.fun + '()')
		
		arglist = iter_seq(joinit((arg.formatExpr(18) for arg in self.args), ',' + line))
		
		return group(self.fun + '(' + arglist + ')').nest(4)

# 		return group(self.fun + '(' + self.args[0].formatExpr(18) + 
# 			iter_seq(',' + line + arg.formatExpr(18) for arg in self.args[1:]) + ')').nest(4)

class CFieldAccess(CExpression):
	def __init__(self, src, field, args = None, direct = True):
		self.src = src
		self.field = field
		self.args = args
		self.direct = direct
	
	def formatExpr(self, prec = 0):
		op = '.' if self.direct else '->'
		
		s = self.src.formatExpr(0) + op + self.field
		if self.args != None:
			s += group(nest(2, '(' + iter_seq(joinit((arg.formatExpr(18) for arg in self.args), ',' + line))
							+ ')'))
		
		return s


class CUnaryExpr(CExpression):
	def __init__(self, op, x):
		self.op = op
		self.x = x
	
	def formatExpr(self, prec = 0):
		return nest(2, self.op + self.x.formatExpr(3))

class CBinExpr(CExpression):
	@staticmethod
	def reduce(op, args):
		return reduce(lambda a,b: CBinExpr(op,a,b), args)

	def __init__(self, op, x, y):
		self.op = op
		self.x = x
		self.y = y
	
	_prec = {
		'*': 5, '/': 5, '%': 5,
		'+': 6, '-': 6,
		'<<': 7, '>>': 7,
		'<': 8, '<=': 8, '>': 8, '>=': 8,
		'==': 9, '!=': 9,
		'&': 10,
		'^': 11,
		'|': 12,
		'&&': 13,
		'||': 14,
		'=': 15,
		',': 17,
	}
	_lassoc = {'/', '%', '-', '<<', '>>', '<', '<=', '>', '>=', '==', '!='}
	
	def formatExpr(self, prec = 0):
		p = self._prec[self.op]
		rp = p
		if self.op in self._lassoc: rp -= 1
		
		
		fmt = self.x.formatExpr(p) + line + self.op + ' ' + self.y.formatExpr(rp)
		if prec < p or (10 <= prec and prec <= 12 and p <= 6):
			fmt = group(nest(2, '(' + fmt + ')'))
		elif prec > p:
			fmt = group(fmt).nest(2)

		return fmt

class CAssign(CExpression):
  def __init__(self, x, y):
    self.x = x
    self.y = y

  _prec = 15
  def formatExpr(self, prec=18):

    fmt = seq(self.x.formatExpr(14), ' =', line, self.y.formatExpr(15))
    if prec < self._prec:
      fmt = seq('(', fmt, ')')
    if prec != self._prec:
      fmt = nest(self.INDENT, group(fmt))

    return fmt

class CStatement(CFragment):
	def pprint(self, width=80):
		self.format().pprint(width)

class CIf(CStatement):
	def __init__(self, condition, then_block, else_block=[]):
		self.condition = condition
		self.then_block = then_block
		self.else_block = else_block
	
	def format(self):
		f = 'if (' + group(nest(4, self.condition.formatExpr(18) + ')') + line) + '{' + \
			nest(4, iter_seq(line + s.format() for s in self.then_block)) + line + '}'
		
		if self.else_block:
			f = f + ' else {' + nest(4, iter_seq(line + s.format() for s in self.else_block)) + line + '}'
		
		return f


class CDefinition(CStatement):
  @classmethod
  def init(cls, ctype, lval, init):
    return cls(
      CTypeName(ctype.underlying_type()),
      CAssign(ctype.decorate(lval), init))

  @classmethod
  def block(cls, var_types):
    '[CType * CVariable] -> [CDefinition]'

    decls = defaultdict(list)
    for ctype, var in var_types:
      decls[ctype.underlying_type()].append(ctype.decorate(var))

    for ctype, vars in decls.iteritems():
      yield cls(CTypeName(ctype), *vars)

  def __init__(self, ctype, *inits):
    assert isinstance(ctype, CType)
    assert all(isinstance(init, CExpression) for init in inits)

    self.ctype = ctype
    self.inits = inits

  def format(self):
    inits = (i.formatExpr(17) for i in self.inits)
    return nest(self.INDENT,
      group(
        seq(
          self.ctype.format(),
          ' ',
          iter_seq(joinit(inits, ',' + line)),
          ';')))


class CReturn(CStatement):
	def __init__(self, ret = None):
		assert ret == None or isinstance(ret, CExpression)
		self.ret = ret

	def format(self):
		f = text('return')
		if self.ret != None:
			f += nest(2, line + self.ret.formatExpr(18))
		f += ';'
		return group(f)

test = CIf(CBinExpr('&&', CTest('foo'), CBinExpr('&&', CTest('bar'), CTest('baz'))),
	[CTest('stmt'), CTest('stmt')])

test2 = CIf(CBinExpr('&&', CTest('foo'), CBinExpr('&&', CTest('bar'), CTest('baz'))),
	[CTest('stmt'), CTest('stmt')], [CTest('stmt'), CTest('stmt')])


if __name__ == '__main__':
	a,b,c,d,e = (CVariable(n) for n in ('alpha','beta','gamma','delta','epsilon'))

	CIf(CBinExpr('==', a, b), [CTest('stmt')]).pprint()

	x = CIf(CBinExpr('&&', 
			CBinExpr('==', a, b),
			CBinExpr('&&',
				CBinExpr('==', a, b),
				CBinExpr('&&',
					CBinExpr('<=', CBinExpr('|', d, e), c),
					CBinExpr('<=', c,	CBinExpr('&', d, e))))),
		[CTest('statement')],
		[CTest('stmt'), CTest('stmt')])
	x.pprint(120)
	x.pprint(80)
	x.pprint(30)
	
	f = lambda x,y: CFunctionCall('WillNotOverflowSignedAdd', x, y)
	
	x = CBinExpr('||', a, CBinExpr('||', CBinExpr('&&', f(c,e), f(c,b)), d))
	x.pprint(80)
	x.pprint(40)
#	x.pprint(20)
#	x.pprint(10)
	
	y = CBinExpr('&&', a, CBinExpr('&&', CBinExpr('||', f(b,c), f(b,e)), d))
	y.pprint(80)
	y.pprint(40)
#	y.pprint(20)
#	y.pprint(10)