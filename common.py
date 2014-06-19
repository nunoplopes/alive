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

def mk_and(l):
  if len(l) == 0:
    return BoolVal(True)
  if len(l) == 1:
    return l[0]
  return And(l)


def mk_or(l):
  if len(l) == 0:
    return BoolVal(False)
  if len(l) == 1:
    return l[0]
  return Or(l)


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


def truncateOrPad(src, tgt):
  srcb = src.sort().size()
  tgtb = tgt.sort().size()
  if srcb == tgtb:
    return src
  if srcb > tgtb:
    return Extract(srcb - 1, srcb - tgtb, src)
  return Concat(src, BitVecVal(0, tgtb - srcb))
