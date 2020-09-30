# Copyright 2014-2018 The Alive authors.
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



import argparse, os, shutil, subprocess, sys, tempfile
from parser import preparse_opt_file


# This forks out multiple copies of Alive concurrently to get better throughput
# on multi-core machines.

# We run this many alive processes in parallel.
PARALLEL_JOBS = 56

def main():
  parser = argparse.ArgumentParser()
  parser.add_argument('file', type=argparse.FileType('r'), nargs='*',
    help='optimization file (read from stdin if none given)',)
  args = parser.parse_args(sys.argv[1:])

  preparsed_opts = sum([preparse_opt_file(f.read()) for f in args.file], [])
  tempdir = tempfile.mkdtemp()
  print('Using temporary directory {0}'.format(tempdir))

  makefile_file_name = os.path.join(tempdir, 'Makefile')
  with open(makefile_file_name, 'a') as f:
    f.write('PYTHON = python\n')
    f.write('ALIVE_HOME = {0}\n'.format(os.getcwd()))

  for i in range(0, len(preparsed_opts)):
    input_file_name = os.path.join(tempdir, 'input-' + str(i))
    output_file_name = os.path.join(tempdir, 'output-' + str(i))
    with open(input_file_name, 'w') as f:
      f.write(preparsed_opts[i])
    with open(makefile_file_name, 'a') as f:
      f.write('test_{0}:\n'.format(i))
      f.write('\tcd $(ALIVE_HOME) && ($(PYTHON) alive.py --hide-progress {0} || echo "FAILED") &> {1}\n'\
              .format(input_file_name, output_file_name))

  all_results_file_name = os.path.join(tempdir, 'all_results')
  with open(makefile_file_name, 'a') as f:
    f.write('all: {0}\n'.format(' '.join('test_{0}'.format(i) for i in range(0, len(preparsed_opts)))))
    for i in range(0, len(preparsed_opts)):
      input_file_name = os.path.join(tempdir, 'input-' + str(i))
      output_file_name = os.path.join(tempdir, 'output-' + str(i))
      f.write('\tcat {0} >> {1}\n'.format(output_file_name, all_results_file_name))
  old_dir = os.getcwd()
  os.chdir(tempdir)
  print('Invoking make to run {0} copies of alive in parallel ...'.format(PARALLEL_JOBS))
  with open(os.devnull, 'w') as devnull:
    subprocess.call(['make', '-j' + str(PARALLEL_JOBS), 'all'],
                    stdout=devnull, stderr=subprocess.STDOUT)
  with open(all_results_file_name, 'r') as all_results:
    print(''.join(all_results.readlines()))
  os.chdir(old_dir)
  shutil.rmtree(tempdir)

if __name__ == '__main__':
  main()
