from z3 import *

# 创建字符串变量

n1 = String('n[1]')
n1_prime = String('n[1]\'')
x = Bool('x')
x_prime = Bool('x\'')
n2 = String('n[2]')
n2_prime = String('n[2]\'')

# variables = {"n[1]":String('n[1]'),"n[1]'":String('n[1]\''),"x":Bool('x'),
#              "x'":Bool('x\''),"n[2]":String('n[2]'),"n[2]'":String('n[2]\'')}
#
# for key,value in variables.items():
#     print(key,":",type(value))

# 创建求解器
solver = Solver()

# 约束条件
solver.add(And(n1=="I"))
solver.add(And(n1_prime=="T"))
solver.add(And(n2==n2_prime,x==x_prime))
solver.add(And(n1_prime=="T",x_prime==False,n2_prime=="T"))
solver.add(Not(And(n1=="T", x==False, n2=="T")))

# solver.add(Implies(True,True))
#
# solver.add(And(variables["n[1]"]=="T",variables["x"]==True))
# solver.add(And(variables["n[1]'"]=="C",variables["x'"]==False))
# solver.add(variables["n[2]"]==variables["n[2]'"])
# solver.add(And(variables["n[1]'"]=="C",variables["n[2]'"]=="C"))

# 检查解的存在性
print(solver.check())



# 获取模型
if solver.check() == sat:
    model = solver.model()
    print(model)
#
# if solver.check() == sat:
#     model = solver.model()
#     print(model)
#     print(model[variables["n[1]"]])
#     # print("n[1]=",model[n1])
#     # print("n[2]=",model[n2])
#     # print("x=",model[x])

