# Copyright 2014 The ALIVe authors.
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

import re
from pyparsing.pyparsing import *
from language import *
from precondition import *

# enable memoization of parsing elements. Gives a nice speedup for large files.
ParserElement.enablePackrat()

# Parsing phases
Source, Target, Pre = range(3)


def pa(fn):
  def z(loc, toks):
    save_loc(loc)
    return fn(toks)
  return z

def parseIntType(toks):
  t = IntType(toks[1])
  for i in range(len(toks)-2):
    t = PtrType(t)
  return t

def parseArrayType(toks):
  t = ArrayType(parseCnstVar(toks[1]), toks[3])
  for i in range(len(toks)-5):
    t = PtrType(t)
  return t

def parseNamedType(toks):
  t = NamedType(toks[0])
  for i in range(len(toks)-1):
    t = PtrType(t)
  return t

def parseOptType(toks):
  if len(toks) == 1:
    return toks[0]
  return UnknownType()

def parseOperand(v, type):
  global identifiers

  if isinstance(v, (ParseResults, list)):
    (loc, v, loc_end) = v
    v = v[0] if isinstance(v, ParseResults) else v
    save_loc(loc)

  if isinstance(v, Value):
    key = v.getUniqueName()
    if not identifiers.has_key(key):
      identifiers[key] = v
    return v

  # %var
  if v[0] == '%' or v[0] == 'C':
    if identifiers.has_key(v):
      return identifiers[v]
    if parsing_phase == Target:
      raise ParseError('Cannot declare new input variables or constants in '
                       'Target')
    if parsing_phase == Pre:
      raise ParseError('Cannot declare new input variables or constants in '
                       'the precondition')
    if v[0] == 'C':
      type = type.ensureIntType()
    identifiers[v] = var = Input(v, type)
    return var

  if v == 'undef':
    c = UndefVal(type)
  elif v == 'true':
    c = ConstantVal(1, type.ensureIntType(1))
  elif v == 'false':
    c = ConstantVal(0, type.ensureIntType(1))
  elif v == 'null':
    c = ConstantVal(0, type.ensurePtrType())
  else:
    c = ConstantVal(int(v), type.ensureIntType())

  identifiers[c.getUniqueName()] = c
  return c

def parseTypeOperand(toks):
  return [toks[0], parseOperand(toks[1], toks[0])]

def parseIntOperand(toks):
  t = toks[0].ensureIntType()
  return [t, parseOperand(toks[1], t)]

def parsePtrOperand(toks):
  t = toks[0].ensurePtrType()
  return [t, parseOperand(toks[1], t)]

def parseOptional(default):
  return lambda toks : toks[0] if len(toks) == 1 else\
                       toks if len(toks) > 0 else default

def parseBinOp(toks):
  type = toks[2].ensureIntType()
  return BinOp(BinOp.getOpId(toks[0]), type, parseOperand(toks[3], type),
               parseOperand(toks[4], type), toks[1])

def parseConversionOp(toks):
  op = ConversionOp.getOpId(toks[0])
  if ConversionOp.enforceIntSrc(op):
    stype = toks[1].ensureIntType()
  elif ConversionOp.enforcePtrSrc(op):
    stype = toks[1].ensurePtrType()
  else:
    stype = toks[1]

  if ConversionOp.enforceIntTgt(op):
    type = toks[3].ensureIntType()
  elif ConversionOp.enforcePtrTgt(op):
    type = toks[3].ensurePtrType()
  else:
    type = toks[3]

  return ConversionOp(op, stype, parseOperand(toks[2], stype), type)

def parseIcmp(toks):
  return Icmp(toks[1], toks[2], toks[3], parseOperand(toks[4], toks[2]))

def parseSelect(toks):
  t = getMostSpecificType(toks[2], toks[4])
  return Select(t, parseOperand(toks[1], IntType(1)),
                parseOperand(toks[3], t), parseOperand(toks[5], t))

def parseOptionalNumElems(loc, toks):
  t = IntType()
  return toks if len(toks) == 2 else [t, parseOperand([loc, '1', loc], t)]

def parseAlloca(toks):
  return Alloca(toks[1], toks[2], toks[3], toks[4])

def parseGEP(toks):
  inbounds = isinstance(toks[1], str)
  if inbounds:
    del toks[1]
  return GEP(toks[1], toks[2], toks[3:], inbounds)

def parseLoad(toks):
  return Load(toks[1], toks[2], toks[3])

def parseOperandInstr(toks):
  op = parseOperand(toks[1], toks[0])
  return CopyOperand(op, toks[0])

def parseStore(toks):
  global identifiers
  s = Store(toks[1], toks[2], toks[3], toks[4], toks[5])
  identifiers[s.getUniqueName()] = s


def parseInstr(toks):
  global identifiers

  reg = toks[0]
  if identifiers.has_key(reg):
    raise ParseError('Redefinition of register')

  toks[1].setName(reg)
  identifiers[reg] = toks[1]
  return


################################
# Constant expr language

def parseCnstVar(v):
  if isinstance(v, Value):
    return v

  (loc, id, loc_end) = v
  if isinstance(id, Value):
    return id

  if re.match(r"(?:-\s*)?\d+", id):
    return ConstantVal(int(id), IntType())

  save_loc(loc)
  if id[0] == '%':
    raise ParseError('Only constants allowed in expressions')

  if identifiers.has_key(id):
    return identifiers[id]

  if parsing_phase == Pre:
    raise ParseError('Identifier used in precondition was not defined')

  return parseOperand(v, IntType())

def check_not_src():
  if parsing_phase == Source:
    raise ParseError('Expressions not allowed in Source')

def parseCnstFunction(toks):
  check_not_src()
  op = CnstFunction.getOpId(toks[0])
  args = [parseOperand(toks[i], UnknownType()) for i in range(1, len(toks))]
  return CnstFunction(op, args, IntType())

def parseRecursive(toks, l):
  toks = toks[0]
  if len(toks) == 1:
    return toks[0]
  return parseRecursive([[l(toks[0], toks[1], toks[2])] + toks[3:]], l)

def parseBinaryPred(toks):
  def z(a,op,b):
    a = parseCnstVar(a)
    check_not_src()
    return CnstBinaryOp(CnstBinaryOp.getOpId(op), a, parseCnstVar(b))
  return parseRecursive(toks, z)

def parseUnaryPred(toks):
  check_not_src()
  op = CnstUnaryOp.getOpId(toks[0][0])
  return CnstUnaryOp(op, parseCnstVar(toks[0][1]))


ParserElement.DEFAULT_WHITE_CHARS = " \t\r"
identifier = Word(srange("[a-zA-Z0-9_.]"))
comma = Suppress(',')
pred_args = Forward()

cnst_expr_atoms = (identifier + Suppress('(') + pred_args + Suppress(')')).\
                    setParseAction(pa(parseCnstFunction)) |\
                  Regex(r"C\d*|(?:-\s*)?\d+|%[a-zA-Z0-9_.]+")
cnst_expr_atoms = locatedExpr(cnst_expr_atoms)

cnst_expr = infixNotation(cnst_expr_atoms,
                          [(Regex(r"~|-(?!\s*\d)"), 1, opAssoc.RIGHT, parseUnaryPred),
                           (oneOf('* /'), 2, opAssoc.LEFT, parseBinaryPred),
                           (oneOf('+ -'), 2, opAssoc.LEFT, parseBinaryPred),
                           (oneOf('<< >>'), 2, opAssoc.LEFT, parseBinaryPred),
                           (Literal('&'), 2, opAssoc.LEFT, parseBinaryPred),
                           (Literal('|'), 2, opAssoc.LEFT, parseBinaryPred),
                          ])

pred_args <<= (cnst_expr + ZeroOrMore(comma + cnst_expr)) | Empty()


################################
# Template program language

reg = Regex(r"%[a-zA-Z0-9_.]+")
opname = identifier
posnum = Word(nums).setParseAction(pa(lambda toks : int(toks[0])))

comment = Suppress(Literal(';') + restOfLine())

type = Forward()
type <<= (Literal('i') + posnum + ZeroOrMore(Literal('*'))).\
           setParseAction(pa(parseIntType)) |\
         (Literal('[') + cnst_expr + Literal('x') + type + Literal(']') +\
           ZeroOrMore(Literal('*'))).setParseAction(pa(parseArrayType)) |\
         (Regex(r"Ty[0-9]*") + ZeroOrMore(Literal('*'))).\
           setParseAction(pa(parseNamedType))

opttype = Optional(type).setParseAction(pa(parseOptType))

flags = ZeroOrMore(Literal('nsw') | Literal('nuw') | Literal('exact')).\
        setParseAction(pa(lambda toks : [toks]))
operand = cnst_expr |\
          (locatedExpr(Literal('false') | Literal('true') | Literal('undef') |\
                       Literal('null')))

typeoperand = (opttype + operand).setParseAction(pa(parseTypeOperand))
intoperand  = (opttype + operand).setParseAction(pa(parseIntOperand))
ptroperand  = (opttype + operand).setParseAction(pa(parsePtrOperand))

binop = (opname + flags + opttype + operand + comma + operand).\
          setParseAction(pa(parseBinOp))

conversionop = (opname + opttype + operand +\
                Optional(Suppress('to') + type).\
                 setParseAction(pa(parseOptType))).\
                   setParseAction(pa(parseConversionOp))

optionalname = Optional(identifier).setParseAction(pa(parseOptional('')))

icmp = (Literal('icmp') + optionalname + typeoperand + comma + operand).\
         setParseAction(pa(parseIcmp))

select = (Literal('select') + Suppress(Optional('i1')) + operand +\
          comma + opttype + operand + comma + opttype + operand).\
            setParseAction(pa(parseSelect))

align = (comma + Suppress('align') + posnum)
optalign = Optional(align).setParseAction(pa(parseOptional(0)))

alloca = (Literal('alloca') + opttype +\
          Optional(comma + intoperand).\
            setParseAction(parseOptionalNumElems) +\
          optalign).setParseAction(pa(parseAlloca))

gep = (Literal('getelementptr') + Optional('inbounds') + ptroperand +\
       ZeroOrMore(comma + intoperand)).setParseAction(pa(parseGEP))

load = (Literal('load') + ptroperand + optalign).setParseAction(pa(parseLoad))

operandinstr = (opttype + operand).setParseAction(pa(parseOperandInstr))

op = operandinstr | icmp | select | alloca | gep | load | binop | conversionop

store = (Literal('store') + typeoperand + comma + ptroperand +\
         optalign).setParseAction(pa(parseStore))

instr = (reg + Suppress('=') + op).setParseAction(pa(parseInstr)) |\
        store | comment

instrc = instr + Optional(comment)
prog = instrc + ZeroOrMore(Suppress(OneOrMore(LineEnd())) + instrc) +\
       Suppress(Optional(White())) + StringEnd()


def parse_llvm(txt):
  global identifiers
  if parsing_phase == Target:
    old_ids = identifiers
    identifiers = collections.OrderedDict()
    for name, val in old_ids.iteritems():
      if isinstance(val, Input):
        identifiers[name] = val
  else:
    identifiers = collections.OrderedDict()
  prog.parseString(txt)
  return identifiers


##########################
def parseBoolPredicate(toks):
  op = LLVMBoolPred.getOpId(toks[0])
  args = []
  for i in range(1, len(toks)):
    a = parseOperand(toks[i], UnknownType())
    args += [a]
    (ok, ex) = LLVMBoolPred.argAccepts(op, i, a)
    if not ok:
      raise ParseError('Operand not allowed. Expected ' + ex)
  return LLVMBoolPred(op, args)

def parseBoolPred(toks):
  from itertools import izip
  lhs = parseCnstVar(toks[0])
  rest = iter(toks[1:])
  cmps = []

  for optok, rhstok in izip(rest,rest):
    op = BinaryBoolPred.getOpId(optok)
    rhs = parseCnstVar(rhstok)
    cmps.append(BinaryBoolPred(op, lhs, rhs))
    lhs = rhs

  if len(cmps) > 1: return PredAnd(*cmps)
  return cmps[0]

def parsePreNot(toks):
  return PredNot(toks[0][0])

def parsePreAnd(toks):
  return PredAnd(*toks[0])

def parsePreOr(toks):
  return PredOr(*toks[0])


ParserElement.DEFAULT_WHITE_CHARS = " \n\t\r"
pre_bool_expr = (cnst_expr + OneOrMore(oneOf('== != < <= > >=') + cnst_expr)).\
                  setParseAction(pa(parseBoolPred))

predicate = (identifier + Suppress('(') + pred_args + Suppress(')')).\
              setParseAction(pa(parseBoolPredicate)) |\
            Literal('true').setParseAction(pa(lambda toks: TruePred())) |\
            pre_bool_expr

pre_expr = infixNotation(predicate,
                         [(Suppress('!'), 1, opAssoc.RIGHT, parsePreNot),
                          (Suppress('&&'), 2, opAssoc.LEFT, parsePreAnd),
                          (Suppress('||'), 2, opAssoc.LEFT, parsePreOr),
                         ])

pre = pre_expr + Optional(comment) + StringEnd() |\
      StringEnd().setParseAction(pa(lambda toks: TruePred()))

def parse_pre(txt, ids):
  global identifiers
  identifiers = ids
  return pre.parseString(txt)[0]


##########################
opt_id = 1

def _parseOpt(s, loc, toks):
  global opt_id, parsing_phase
  name = str(opt_id)
  opt_id += 1
  pre = ''
  pre_line = 0
  src = tgt = None

  skip = False
  for i in range(len(toks)):
    if skip:
      skip = False
      continue

    if toks[i] == 'Name:':
      name = toks[i+1]
      i += 1
      skip = True
    elif toks[i] == 'Pre:':
      pre = toks[i+1][1]
      pre_line = lineno(toks[i+1][0], s)
      i += 1
      skip = True
    elif src is None:
      src = toks[i][1]
      src_line = lineno(toks[i][0], s)
    else:
      assert tgt is None
      tgt = toks[i][1]
      tgt_line = lineno(toks[i][0], s)

  parsing_phase = Source
  save_parse_str(src, src_line)
  src = parse_llvm(src)

  parsing_phase = Target
  save_parse_str(tgt, tgt_line)
  tgt = parse_llvm(tgt)

  parsing_phase = Pre
  save_parse_str(pre, pre_line)
  pre = parse_pre(pre, src)
  return name, pre, src, tgt

def parseOpt(s, loc, toks):
  try:
    return _parseOpt(s, loc, toks)
  except ParseException, e:
    print exception2str(e.msg, e.line, e.lineno, e.col)
    exit(-1)


comments = Suppress(Optional(White()) + ZeroOrMore(comment + White()))

opt = comments +\
       (Optional(Literal('Name:') + SkipTo(LineEnd())) +\
       comments +\
       Optional(Literal('Pre:') + locatedExpr(SkipTo(LineEnd()))) +\
       locatedExpr(SkipTo('=>')) + Suppress('=>') +\
       locatedExpr(SkipTo(Literal('Name:') | StringEnd()))).\
         setParseAction(parseOpt)

opt_file = OneOrMore(opt) + StringEnd()


def parse_opt_file(txt):
  try:
    return opt_file.parseString(txt)
  except ParseException, e:
    print exception2str(e.msg, e.line, e.lineno, e.col, 0)
    exit(-1)
  except ParseError, e:
    print e
    exit(-1)
