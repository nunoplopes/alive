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

from pyparsing.pyparsing import *
from language import *
from precondition import *

# enable memoization of parsing elements. Gives a nice speedup for large files.
ParserElement.enablePackrat()


def parseIntType(toks):
  t = IntType(toks[1])
  for i in range(len(toks)-2):
    t = PtrType(t)
  return t

def parseArrayType(toks):
  t = ArrayType(toks[1], toks[3])
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

def parseOperand(toks, type):
  global identifiers

  # %var
  if len(toks) == 2 or toks[0][0] == 'C':
    reg = '%' + toks[1] if len(toks) == 2 else toks[0]
    if identifiers.has_key(reg):
      return identifiers[reg]
    identifiers[reg] = v = Input(reg, type)
    return v

  assert len(toks) == 1
  if toks[0] == 'undef':
    c = UndefVal(type)
  elif toks[0] == 'true':
    c = Constant(1, type.ensureIntType(1))
  elif toks[0] == 'false':
    c = Constant(0, type.ensureIntType(1))
  elif toks[0] == 'null':
    c = Constant(0, type.ensurePtrType())
  else:
    c = Constant(int(toks[0]), type.ensureIntType())

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

def parseOptionalNumElems(toks):
  t = IntType()
  return toks if len(toks) == 2 else [t, parseOperand(['1'], t)]

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

  reg = '%' + toks[1]
  if identifiers.has_key(reg):
    print 'Redifinition of ' + reg
    exit(-1)

  toks[2].setName(reg)
  identifiers[reg] = toks[2]
  return


identifier = Word(srange("[a-zA-Z0-9_.]"))
reg = Literal('%') + identifier
opname = identifier
posnum = Word(nums).setParseAction(lambda toks : int(toks[0]))
intconst = Regex(r"C[0-9]*")
posnumOrConst = (Word(nums) | intconst).\
                  setParseAction(lambda toks : parseOperand(toks[0], IntType()))

comment = Literal(';') + restOfLine()

type = Forward()
type <<= (Literal('i') + posnum + ZeroOrMore(Literal('*'))).\
           setParseAction(parseIntType) |\
         (Literal('[') + posnumOrConst + Literal('x') + type + Literal(']') +\
           ZeroOrMore(Literal('*'))).setParseAction(parseArrayType) |\
         (Regex(r"Ty[0-9]*") + ZeroOrMore(Literal('*'))).\
           setParseAction(parseNamedType)

opttype = Optional(type).setParseAction(parseOptType)

flags = ZeroOrMore(Literal('nsw') | Literal('nuw') | Literal('exact')).\
        setParseAction(lambda toks : [toks])
operand = (reg | Regex(r"-?[0-9]+") | intconst | Literal('false') |\
           Literal('true') | Literal('undef') | Literal('null')).\
             setParseAction(lambda toks : [toks])

typeoperand = (opttype + operand).setParseAction(parseTypeOperand)
intoperand  = (opttype + operand).setParseAction(parseIntOperand)
ptroperand  = (opttype + operand).setParseAction(parsePtrOperand)
comma = Literal(',').suppress()

binop = (opname + flags + opttype + operand + comma + operand).\
          setParseAction(parseBinOp)

conversionop = (opname + opttype + operand +\
                Optional(Literal('to').suppress() + type).\
                 setParseAction(parseOptType)).setParseAction(parseConversionOp)

optionalname = Optional(identifier).setParseAction(parseOptional(''))

icmp = (Literal('icmp') + optionalname + typeoperand + comma + operand).\
         setParseAction(parseIcmp)

select = (Literal('select') + Optional(Literal('i1')).suppress() + operand +\
          comma + opttype + operand + comma + opttype + operand).\
            setParseAction(parseSelect)

align = (comma + Suppress('align') + posnum)
optalign = Optional(align).setParseAction(parseOptional(0))

alloca = (Literal('alloca') + opttype +\
          Optional(comma + intoperand).setParseAction(parseOptionalNumElems) +\
          optalign).setParseAction(parseAlloca)

gep = (Literal('getelementptr') + Optional(Literal('inbounds')) + ptroperand +\
       ZeroOrMore(comma + intoperand)).setParseAction(parseGEP)

load = (Literal('load') + ptroperand + optalign).setParseAction(parseLoad)

operandinstr = (opttype + operand).setParseAction(parseOperandInstr)

op = operandinstr | icmp | select | alloca | gep | load | binop | conversionop

store = (Literal('store') + typeoperand + comma + ptroperand +\
         optalign).setParseAction(parseStore)

instr = (reg + Suppress('=') + op).setParseAction(parseInstr) |\
        store | comment.suppress()

prog = OneOrMore(instr) + StringEnd()


def parse_llvm(txt):
  global identifiers
  try:
    identifiers = collections.OrderedDict()
    prog.parseString(txt)
    return identifiers
  except ParseException, e:
    print 'Parsing error:'
    print e
    exit(-1)


##########################
def parsePredArg(toks):
  id = toks[0]
  if id.isdigit():
    return PredConst(int(id))

  if identifiers.has_key(id):
    return PredVar(identifiers[id])
  print 'Identifier used in precondition was not defined: ' + id
  exit(-1)

def parseBoolPredicate(toks):
  op = LLVMBoolPred.getOpId(toks[0])
  return LLVMBoolPred(op, toks[1:])

def parseValFunction(toks):
  op = ValFunction.getOpId(toks[0])
  try:
    return ValFunction(op, toks[1:], IntType())
  except Exception, e:
    print e
    exit(-1)

def parseRecursive(toks, l):
  toks = toks[0]
  if len(toks) == 1:
    return toks[0]
  return parseRecursive([[l(toks[0], toks[1], toks[2])] + toks[3:]], l)

def parseBinaryPred(toks):
  return parseRecursive(toks, lambda a,op,b:
                                BinaryValPred(BinaryValPred.getOpId(op), a, b))

def parseUnaryPred(toks):
  op = UnaryValPred.getOpId(toks[0][0])
  return UnaryValPred(op, toks[0][1])

def parseBoolPred(toks):
  op = BinaryBoolPred.getOpId(toks[1])
  return BinaryBoolPred(op, toks[0], toks[2])

def parsePreNot(toks):
  return PredNot(toks[0][0])

def parsePreAnd(toks):
  return parseRecursive(toks, lambda a,op,b: PredAnd(a, b))

def parsePreOr(toks):
  return parseRecursive(toks, lambda a,op,b: PredOr(a, b))

pred_args = Forward()

#pre_expr_atoms = (reg | Regex(r"-?[0-9]+") | intconst) ---  TOO SLOW
pre_expr_atoms = (identifier + Suppress('(') + pred_args + Suppress(')')).\
                   setParseAction(parseValFunction) |\
                 Word(srange("[a-zA-Z0-9_.%]")).setParseAction(parsePredArg)

pre_expr = infixNotation(pre_expr_atoms,
                         [(oneOf('- ~'), 1, opAssoc.RIGHT, parseUnaryPred),
                          (oneOf('* / %'), 2, opAssoc.LEFT, parseBinaryPred),
                          (oneOf('+ -'), 2, opAssoc.LEFT, parseBinaryPred),
                          (Literal('>>'), 2, opAssoc.LEFT, parseBinaryPred),
                          (Literal('<<'), 2, opAssoc.LEFT, parseBinaryPred),
                          (Literal('&'), 2, opAssoc.LEFT, parseBinaryPred),
                          (Literal('|'), 2, opAssoc.LEFT, parseBinaryPred),
                         ])

pre_bool_expr = (pre_expr + oneOf('== !=') + pre_expr).\
                  setParseAction(parseBoolPred)

#pred_arg = (reg | intconst).setParseAction(parsePredArg)
pred_arg = pre_expr_atoms
pred_args <<= (pred_arg + ZeroOrMore(comma + pred_arg)) | Empty()
predicate = (identifier + Suppress('(') + pred_args + Suppress(')')).\
              setParseAction(parseBoolPredicate) |\
            Literal('true').setParseAction(lambda toks: TruePred()) |\
            pre_bool_expr

pre = infixNotation(predicate,
                    [(Suppress('!'), 1, opAssoc.RIGHT, parsePreNot),
                     (Literal('&&'), 2, opAssoc.LEFT, parsePreAnd),
                     (Literal('||'), 2, opAssoc.LEFT, parsePreOr),
                    ]) |\
      StringEnd().setParseAction(lambda toks: TruePred())

def parse_pre(txt, ids):
  global identifiers
  try:
    identifiers = ids
    return pre.parseString(txt)[0]
  except ParseException, e:
    print 'Parsing error in precondition:'
    print e
    exit(-1)


##########################
opt_id = 1

def parseOpt(toks):
  global opt_id
  name = str(opt_id)
  opt_id += 1
  pre = ''
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
      pre = toks[i+1]
      i += 1
      skip = True
    elif src is None:
      src = toks[i]
    else:
      assert tgt is None
      tgt = toks[i]

  src = parse_llvm(src)
  tgt = parse_llvm(tgt)
  pre = parse_pre(pre, src)
  return name, pre, src, tgt


opt = (Optional(Literal('Name:') + SkipTo(LineEnd())) +\
       Optional(Literal('Pre:') + SkipTo(LineEnd())) +\
       SkipTo('=>') + Literal('=>').suppress() +\
       SkipTo(Literal('Name:') | StringEnd())).\
         setParseAction(parseOpt)

opt_file = OneOrMore(opt)


def parse_opt_file(txt):
  try:
    return opt_file.parseString(txt)
  except ParseException, e:
    print 'Parsing error:'
    print e
    exit(-1)
