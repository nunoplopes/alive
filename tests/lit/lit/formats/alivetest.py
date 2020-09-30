
import re, string, subprocess, signal

import lit.Test
from .base import FileBasedTest


def executeCommand(command, input):
  p = subprocess.Popen(command,
                       stdin=subprocess.PIPE,
                       stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE)
  p.stdin.write(input)
  out,err = p.communicate()
  exitCode = p.wait()

  # Detect Ctrl-C in subprocess.
  if exitCode == -signal.SIGINT:
    raise KeyboardInterrupt

  # Ensure the resulting output is always of string type.
  try:
    out = str(out.decode('ascii'))
  except:
    out = str(out)
  try:
    err = str(err.decode('ascii'))
  except:
    err = str(err)

  return out, err, exitCode


def readFile(path):
  fd = open(path, 'r')
  return fd.read()


class AliveTest(FileBasedTest):
  def __init__(self):
    self.regex = re.compile(r";\s*(ERROR:.*)")
    self.regex_args = re.compile(r";\s*TEST-ARGS:(.*)")

  def execute(self, test, litConfig):
    test = test.getSourcePath()
    cmd = ['python', 'alive.py']
    input = readFile(test)

    # add test-specific args
    m = self.regex_args.search(input)
    if m != None:
      cmd += m.group(1).split()

    out, err, exitCode = executeCommand(cmd, input)

    m = self.regex.search(input)
    if m == None:
      if exitCode == 0 and string.find(out, 'Optimization is correct!') != -1:
        return lit.Test.PASS, ''
      return lit.Test.FAIL, out + err

    if exitCode == 255 and string.find(out, m.group(1)) != -1:
      return lit.Test.PASS, ''
    return lit.Test.FAIL, out + err
