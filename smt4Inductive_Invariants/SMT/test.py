import subprocess
ivyFilePath = "../protocols/test/test.ivy"
ivy_process = subprocess.Popen("ivy_check {0}".format(ivyFilePath), shell=True,
                                    stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE)
(stdout, stderr) = ivy_process.communicate()
if "OK" in str(stdout):
    print("Inductive invariants already generated ! \n")
else:
    print("Can't pass IVY's check ! \n")
    print("Error messages during the runtime are as follows:")
    print(stdout.decode())