import os
import subprocess
import re

import os

cmurphi_path = '../../cmurphi_LS'
file = '../protocols/mutualEx/mutualEx.m'
file = file.split('.m')[0]
# print("file:",file)
process1 = subprocess.Popen("{0}/src/mu {1}.m".format(cmurphi_path,file), shell=True,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE)
(stdout, stderr) = process1.communicate()
if not re.search(r'Code generated', stdout.decode('utf-8')):
    print(stderr.decode('utf-8'))
    raise ValueError

command2 = "g++ -ggdb -o {0}.o {0}.cpp -I {1}/include -lm".format(file, cmurphi_path)
process2 = subprocess.Popen(command2, shell=True,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE)
process2.communicate()
if not os.path.exists("./{0}.o".format(file)): raise FileExistsError


process3 = subprocess.Popen("./{0}.o -localsearch -m 5000".format(file), shell=True,
                           stdout=subprocess.PIPE,
                           stderr=subprocess.PIPE)

(stdoutdata, stderrdata) = process3.communicate()
pattern_counter = re.compile(r'Invariant\s"(\w+).*"\sfailed')
counter_ex = re.findall(pattern_counter, stdoutdata.decode('utf-8'))
if not counter_ex:
    print('No cti found. The invariants are OK.')
    # return True
else:
    print('counter_ex:', counter_ex)
    # return False

os.remove('%s.cpp' % file)
os.remove('%s.o' % file)


