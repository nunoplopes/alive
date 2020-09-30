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

'''
Simple pretty printer.

Based on "Lazy v. Yield: Incremental, Linear Pretty-Printing", by Kiselyov,
Peyton-Jones, and Sabry.
'''

from __future__ import absolute_import
from __future__ import print_function
from collections import deque
from itertools import chain
from six.moves import range

class Doc(object):
  Text, Line, GBegin, GEnd = list(range(4))
  
  def _items(self):
    yield self
  
  def __add__(self, other):
    return seq(self, other)
  
  def __radd__(self, other):
    return seq(other, self)
  
  def __or__(self, other):
    return seq(self, line, other)
  
  def __ror__(self, other):
    return seq(other, line, self)
    
  def nest(self, indent):
    return _Nest(indent, self)
  
  def format(self, width=80, indent=0):
    return ''.join(text_events(width, findGroupEnds(width, addHP(self.events(indent)))))
  
  def __str__(self):
    return self.format()
  
  def pprint(self, width=80, indent=0):
    print(self.format(width, indent))

class _Text(Doc):
  def __init__(self, text):
    assert '\n' not in text
    self.text = text
  
  def events(self, indent):
    yield (Doc.Text, self.text)
  
  def __nonzero__(self):
    return bool(self.text)
    
  def __repr__(self):
    return '_Text({0.text!r})'.format(self)
  
class _Line(Doc):
  def events(self, indent):
    yield (Doc.Line, indent)
  
  def __repr__(self):
    return '_Line()'

class _Group(Doc):
  def __init__(self, doc):
    assert bool(doc)
    self.doc = doc # need to normalize this. maybe before construction?
  
  def events(self, indent):
    yield (Doc.GBegin,)
    for e in self.doc.events(indent):
      yield e
    yield (Doc.GEnd,)
  
  def __repr__(self):
    return '_Group({0.doc!r})'.format(self)

class _Seq(Doc):
  def __init__(self, docs):
    self.docs = docs
  
  def events(self, indent):
    return chain.from_iterable(doc.events(indent) for doc in self.docs)
  
  def _items(self):
    return iter(self.docs)
  
  def __nonzero__(self):
    return any(bool(doc) for doc in self.docs)
  
  def __repr__(self):
    return '_Seq({0.docs!r})'.format(self)

class _Nest(Doc):
  def __init__(self, indent, doc):
    self.indent = indent
    self.doc = doc
  
  def events(self, indent):
    return self.doc.events(indent + self.indent)
  
  def __nonzero__(self):
    return bool(self.doc)
  
  def __repr__(self):
    return '_Nest({0.indent}, {0.doc!r})'.format(self)

def printit(iterable):
  for x in iterable:
    print(x)

def joinit(iterable, delimiter):
  it = iter(iterable)
  yield next(it)
  for x in it:
    yield delimiter
    yield x

def addHP(event_it):
  pos = 0
  for event in event_it:
    if event[0] == Doc.Text:
      pos += len(event[1])
      yield (Doc.Text, pos, event[1])
    elif event[0] == Doc.Line:
      pos += 1
      yield (Doc.Line, pos, event[1])
    else:
      yield (event[0], pos)

class Buf(object):
  def __init__(self):
    self.iter = iter([])
  
  def appendLeft(self, item):
    self.iter = chain(iter([item]), self.iter)
  
  def appendRight(self, item):
    self.iter = chain(self.iter, iter([item]))
  
  def concat(self, other):
    self.iter = chain(self.iter, other.iter)
  
  def emit(self):
    return self.iter

def addGBeg(eventHP_it):
  bufs = []
  for event in eventHP_it:
    if event[0] == Doc.GBegin:
      bufs.append(Buf())

    elif bufs and event[0] == Doc.GEnd:
      pos = event[1]
      buf = bufs.pop()
      buf.appendLeft((Doc.GBegin, pos))
      buf.appendRight(event)
      if bufs:
        bufs[-1].concat(buf)
      else:
        for event in buf.emit():
          yield event
    
    elif bufs:
      bufs[-1].appendRight(event)
    
    else:
      yield event

def findGroupEnds(width, eventHP_it):
  bufs = deque()
  last_hp = 0
  
  for event in eventHP_it:
    #print 'got:', event, 'deque:', len(bufs), 'hpl:', last_hp, 'dl:', [b[0] for b in bufs]
      
    if bufs:
      if event[0] == Doc.GEnd:
        (_, buf) = bufs.pop()
        buf.appendLeft((Doc.GBegin, event[1]))
        buf.appendRight((Doc.GEnd, event[1]))
        if bufs:
          (p, buf2) = bufs.pop()
          buf2.concat(buf)
          bufs.append((p, buf2))
        else:
          for event in buf.emit():
            yield event
      else:
        if event[0] == Doc.GBegin:
          bufs.append((event[1] + width, Buf()))
        else:
          (p, buf) = bufs.pop()
          buf.appendRight(event)
          bufs.append((p, buf))
        
        while last_hp < event[1] or len(bufs) > width:
          yield (Doc.GBegin, None)
          (p, buf) = bufs.popleft()
          for event in buf.emit():
            yield event
          if bufs:
            last_hp = bufs[0][0]
          else:
            break
      
    elif event[0] == Doc.GBegin:
      last_hp = event[1] + width
      bufs.append((last_hp, Buf()))
    else:
      yield event

def text_events(width, event_it):
  fits = 0
  hpl = width
  for event in event_it:
    if event[0] == Doc.Text:
      yield event[2]
    elif event[0] == Doc.Line:
      if fits:
        yield ' '
      else:
        yield '\n' + ' ' * event[2]
        hpl = event[1] + width - event[2]
    elif event[0] == Doc.GBegin:
      if fits:
        fits += 1
      elif event[1] != None:
        fits = 1 if event[1] <= hpl else 0
    else:
      if fits:
        fits -= 1


line = _Line()

def nest(indent, doc):
  return _Nest(indent, doc)
  
def text(string):
  if isinstance(string, Doc):
    return string
  
  if isinstance(string, str):
    return _Text(string)
  
  return _Text(str(string))

def seq(*docs):
  return iter_seq(docs)

def iter_seq(doc_it):
  docs = tuple(chain.from_iterable(text(doc)._items() for doc in doc_it))
  if len(docs) == 1:
    return docs[0]
  return _Seq(docs)
  
def group(doc):
  if isinstance(doc, _Group):
    return doc
  
  if not bool(doc):
    return doc
  
  return _Group(doc)
