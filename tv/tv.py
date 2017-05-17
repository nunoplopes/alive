# Copyright 2014-2017 The Alive authors.
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

import re, subprocess, string, sys, time

opts_per_alive_proc = 20

def txt2opt(txt):
  s = ''
  for l in txt.splitlines()[1:]:
    if l == '}':
      break
    s += l + '\n'
  return s

def rename_opt(txt, skip_id):
  def repl(m):
    n = m.group(1)
    return '%'+n if int(n) < skip_id else '%p' + n
  return re.sub('%(\d+)', repl, txt)

def verify(opt, num_opts):
  if num_opts == 0:
    return
  p = subprocess.Popen(['python', 'alive.py', '--tv'], 4096,
                       stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE)
  (out, err) = p.communicate(opt)
  if out.count('Optimization is correct!') != num_opts or err != '':
    print(out + "\n" + err)
    #sys.stdout.flush()


file = sys.argv[2]

# map storing fn name => optimized IR
optms = {}

start = time.time()
reg = re.compile('func\d+')
for opt in re.split('\ndefine i\d+ @',
                    open(file + '.'+sys.argv[1]+'.ll', 'r').read())[1:]:
  fnname = reg.match(opt).group(0)
  optms[fnname] = txt2opt(opt)

input = open(file + '.ll', 'r').read()
s = ''
i = 0
for orig in re.split('\ndefine i\d+ @', input)[1:]:
  fnname = reg.search(orig).group(0)
  fnargs = orig.splitlines()[0].count(',') + 1
  orig = txt2opt(orig)
  optmz = optms[fnname]
  if orig == optmz:
    continue

  s += 'Name: %s\n' % fnname
  s += orig
  s += '=>\n'
  s += rename_opt(optmz, fnargs) + '\n'
  i += 1
  if i == opts_per_alive_proc:
    verify(s, i)
    s = ''
    i = 0
verify(s, i)

end = time.time()
print('TV_DONE')
print(end-start)
