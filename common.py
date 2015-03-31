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

from z3 import *

gbl_unique_id = 0
def mk_unique_id():
  global gbl_unique_id
  id = str(gbl_unique_id)
  gbl_unique_id += 1
  return id


def fold_ite_list(l):
  if len(l) == 0:
    return None
  cond, val = l[0]
  if len(l) == 1:
    return val
  return If(cond, val, fold_ite_list(l[1:]))


def freshBV(prefix, size):
  return BitVec('%s_%s' % (prefix, mk_unique_id()), size)


def mk_and(l):
  l = [e for e in l if not is_true(e)]
  if len(l) == 0:
    return BoolVal(True)
  if len(l) == 1:
    return l[0]
  return And(l)


def mk_or(l):
  l = [e for e in l if not is_false(e)]
  if len(l) == 0:
    return BoolVal(False)
  if len(l) == 1:
    return l[0]
  return Or(l)


def mk_not(e):
  if is_false(e):
    return BoolVal(True)
  if is_true(e):
    return BoolVal(False)
  return Not(e)


def mk_distinct(l):
  if len(l) < 2:
    return BoolVal(True)
  return Distinct(l)


def mk_implies(a, b):
  if is_true(a):
    return b
  if is_false(a) or is_true(b):
    return BoolVal(True)
  if is_false(b):
    return Not(a)
  return Implies(a, b)


def mk_concat(l):
  if len(l) == 1:
    return l[0]
  return Concat(l)


def mk_forall(l, f):
  if l == []:
    return f
  return ForAll(l, f)


def mk_exists(l, f):
  if l == []:
    return f
  return Exists(l, f)


def toBV(b):
  return If(b, BitVecVal(1, 1), BitVecVal(0, 1))


def truncateOrZExt(src, tgt):
  srcb = src.size()
  if isinstance(tgt, int):
    tgtb = tgt
  else:
    tgtb = tgt.size()
  if srcb == tgtb:
    return src
  if srcb > tgtb:
    return Extract(tgtb - 1, 0, src)
  return ZeroExt(tgtb - srcb, src)


def truncateOrSExt(src, tgt):
  srcb = src.size()
  tgtb = tgt.size()
  if srcb == tgtb:
    return src
  if srcb > tgtb:
    return Extract(tgtb - 1, 0, src)
  return SignExt(tgtb - srcb, src)


def truncateOrPad(src, tgt):
  srcb = src.size()
  tgtb = tgt.size()
  if srcb == tgtb:
    return src
  if srcb > tgtb:
    return Extract(srcb - 1, srcb - tgtb, src)
  return Concat(src, BitVecVal(0, tgtb - srcb))


"""
def no_overflow_smul(a, b):
  size = a.size()
  assert b.size() == size
  m = SignExt(size, a) * SignExt(size, b)
  min = BitVecVal(-(1 << (size-1)), 2*size)
  max = BitVecVal((1 << (size-1)) -1, 2*size)
  return And(m >= min, m <= max)
"""
def no_overflow_smul(a, b):
  size = a.size()
  assert b.size() == size
  m = SignExt(size, a) * SignExt(size, b)
  return m == SignExt(size, a * b)


def no_overflow_umul(a, b):
  size = a.size()
  assert b.size() == size
  m = Extract(2*size-1, size, ZeroExt(size, a) * ZeroExt(size, b))
  return m == BitVecVal(0, size)


def isShiftedMask(a):
  v = (a - 1) | a
  return [v != 0, ((v + 1) & v) == 0]


def bv_log2(v, bitwidth):
  def rec(h, l):
    if h <= l:
      return BitVecVal(l, bitwidth)
    mid = l+int((h-l)/2)
    return If(Extract(h,mid+1,v) != 0, rec(h, mid+1), rec(mid, l))
  return rec(v.size()-1, 0)

"""
linear version of log2
def bv_log2(v, bitwidth):
  def rec(i):
    if i == 0:
      return BitVecVal(0, bitwidth)
    return If(Extract(i,i,v) == BitVecVal(1,1), BitVecVal(i,bitwidth), rec(i-1))
  return rec(v.size()-1)
"""


def ctlz(v, output_width):
  size = v.size()
  def rec(i):
    if i < 0:
      return BitVecVal(size, output_width)
    return If(Extract(i,i,v) == BitVecVal(1, 1),
              BitVecVal(size-1-i, output_width),
              rec(i-1))
  return rec(size-1)


def cttz(v, output_width):
  size = v.size()
  def rec(i):
    if i == size:
      return BitVecVal(size, output_width)
    return If(Extract(i,i,v) == BitVecVal(1, 1),
              BitVecVal(i, output_width),
              rec(i+1))
  return rec(0)


def ComputeNumSignBits(v, bitwidth):
  size = v.size()
  size1 = size - 1
  sign = Extract(size1, size1, v)

  def rec(i):
    if i < 0:
      return BitVecVal(size, bitwidth)
    return If(Extract(i,i,v) == sign,
              rec(i-1),
              BitVecVal(size1-i, bitwidth))
  return rec(size - 2)


##########################
# Type inference utilities

def register_pick_one_type(v):
  global gbl_one_type_only
  gbl_one_type_only.add(str(v))

def unregister_pick_one_type(vs):
  global gbl_one_type_only
  for v in vs.iterkeys():
    gbl_one_type_only.discard(v)

def reset_pick_one_type():
  global gbl_one_type_only
  gbl_one_type_only = set([])

def get_pick_one_type():
  return gbl_one_type_only


##########################

# number of users of an instruction
def get_users_var(name):
  return BitVec('u_' + name, 8)

def get_flag_var(flag, inst):
  dst = 'src' if gbl_is_source else 'tgt'
  return BitVec('f_%s_%s_%s' % (flag, inst, dst), 1)

def set_smt_is_source(s):
  global gbl_is_source
  gbl_is_source = s

gbl_infer_flags = False
def set_infer_flags(f):
  global gbl_infer_flags
  gbl_infer_flags = f

def do_infer_flags():
  return gbl_infer_flags

gbl_use_array_theory = False
def set_use_array_theory(f):
  global gbl_use_array_theory
  gbl_use_array_theory = f

def use_array_theory():
  return gbl_use_array_theory

gbl_ptr_size = 32
def set_ptr_size(m):
  global gbl_ptr_size
  sz = m.get_interp(Int('ptrsize'))
  if sz is not None:
    gbl_ptr_size = sz.as_long()

def get_ptr_size():
  return gbl_ptr_size


##########################
# Error handling

class AliveError(Exception):
  pass

class ParseError():
  def __init__(self, msgs, token = None):
    if isinstance(msgs, list):
      self.msgs = msgs
    else:
      self.msgs = [msgs]
    self.token = token

  def __repr__(self):
    lineno = get_lineno()
    line = get_line(lineno)
    col = get_column(line, self.token)
    return exception2str("\n".join(self.msgs), line, lineno, col)

gbl_line_offset = 0
def exception2str(msg, line, lineno, col, line_offset = None):
  if line_offset is None:
    line_offset = gbl_line_offset
  s  = "ERROR: %s (line: %d)\n" % (msg, line_offset + lineno)
  s += line + '\n'
  s += ' ' * col + '^'
  return s

def get_lineno():
  return gbl_parse_str.count('\n', 0, gbl_parse_loc) + 1

def get_line(lineno):
  return gbl_parse_str.split('\n')[lineno-1]

def get_column(s, tok):
  col = gbl_parse_loc - (gbl_parse_str.rfind('\n', 0, gbl_parse_loc)+1)
  if not tok:
    return col
  token_col = s.find(tok, col)
  return token_col if token_col >= 0 else col

def save_parse_str(s, line):
  global gbl_parse_str, gbl_line_offset
  gbl_parse_str = s
  gbl_line_offset = line-1

def save_loc(loc):
  global gbl_parse_loc
  gbl_parse_loc = loc
