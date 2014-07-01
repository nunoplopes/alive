# Copyright 2014 The ALIVe authors.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from language import *

class Predicate(object):
  def __repr__(self):
    raise '__repr__ not implemented'


################################
class TruePred(Predicate):
  def __repr__(self):
    return 'true'

  def toSMT(self, state, types):
    return BoolVal(True)


################################
class PredAnd(Predicate):
  def __init__(self, v1, v2):
    self.v1 = v1
    self.v2 = v2
    assert isinstance(self.v1, Predicate)
    assert isinstance(self.v2, Predicate)

  def __repr__(self):
    return '(%s && %s)' % (self.v1, self.v2)

  def toSMT(self, state, types):
    return And(self.v1.toSMT(state, types), self.v2.toSMT(state, types))


################################
class PredOr(Predicate):
  def __init__(self, v1, v2):
    self.v1 = v1
    self.v2 = v2
    assert isinstance(self.v1, Predicate)
    assert isinstance(self.v2, Predicate)

  def __repr__(self):
    return '(%s || %s)' % (self.v1, self.v2)

  def toSMT(self, state, types):
    return Or(self.v1.toSMT(state, types), self.v2.toSMT(state, types))


################################
class BoolPredicate(Predicate):
  isSignBit, Last = range(2)

  opnames = {
    isSignBit: 'isSignBit',
  }
  opids = {v:k for k, v in opnames.items()}

  num_args = {
    isSignBit: 1,
  }

  def __init__(self, op, args):
    self.op = op
    self.args = args
    if self.num_args[op] != len(args):
      print 'Wrong number of argument to %s (expected=%d)' %\
        (self.opnames[op], self.num_args[op])
      exit(-1)
    assert op >= 0 and op < self.Last
    for a in self.args:
      assert isinstance(a, Instr)

  def __repr__(self):
    args = [a.getName() for a in self.args]
    return '%s(%s)' % (self.opnames[self.op], ', '.join(args))

  def getOpName(self):
    return self.opnames[self.op]

  @staticmethod
  def getOpId(name):
    try:
      return BoolPredicate.opids[name]
    except:
      print 'Unknown boolean predicate: ' + name
      exit(-1)

  def toSMT(self, state, types):
    args = [state.eval(v, [], []) for v in self.args]
    return {
      self.isSignBit: lambda a: a == (1 << (a.sort().size()-1)),
    }[self.op](*args)
