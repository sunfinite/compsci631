#!/usr/bin/python
import tempfile
import os
import subprocess

binary = '/home/ubuntu/compsci631/run_compiler.sh'
pass_mode = False
fail = []
with open('tests') as f:
    for line in f:
        line = line.strip()
        if not line:
          continue
        if 'pass' in line:
            pass_mode = True
        elif 'xfail' in line:
            pass_mode = False
        else:
            fd, path = tempfile.mkstemp()
            os.write(fd, line)
            os.close(fd)
            p = subprocess.Popen([binary, path], 
              stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            stdout, stderr = p.communicate()
            if p.returncode == 2 and pass_mode:
                fail.append((line, stdout, stderr))
            elif p.returncode == 0 and not pass_mode:
                fail.append((line, stdout, stderr))
            else:
              print "RESULT: %s: %s" % (line, stdout)
            os.remove(path)
print "Number of failures: %d" % len(fail)
for i, f in enumerate(fail):
  print "-" * 42, "\n%d.)  " % (i + 1), f[0], "\nSTDOUT: " + f[1], "\n\nSTDERR: " + f[2]
