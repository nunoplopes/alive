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

from z3 import *

gbl_unique_id = 0
def mk_unique_id():
  global gbl_unique_id
  id = str(gbl_unique_id)
  gbl_unique_id += 1
  return id


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


def mk_forall(l, f):
  if l == []:
    return f
  return ForAll(l, f)


def toBV(b):
  return If(b, BitVecVal(1, 1), BitVecVal(0, 1))


def truncateOrZExt(src, tgt):
  srcb = src.sort().size()
  if isinstance(tgt, int):
    tgtb = tgt
  else:
    tgtb = tgt.sort().size()
  if srcb == tgtb:
    return src
  if srcb > tgtb:
    return Extract(tgtb - 1, 0, src)
  return ZeroExt(tgtb - srcb, src)


def truncateOrSExt(src, tgt):
  srcb = src.sort().size()
  tgtb = tgt.sort().size()
  if srcb == tgtb:
    return src
  if srcb > tgtb:
    return Extract(tgtb - 1, 0, src)
  return SignExt(tgtb - srcb, src)


def truncateOrPad(src, tgt):
  srcb = src.sort().size()
  tgtb = tgt.sort().size()
  if srcb == tgtb:
    return src
  if srcb > tgtb:
    return Extract(srcb - 1, srcb - tgtb, src)
  return Concat(src, BitVecVal(0, tgtb - srcb))


##########################
# Error handling

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
def exception2str(msg, line, lineno, col):
  s  = "ERROR: %s (line: %d)\n" % (msg, gbl_line_offset + lineno)
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
