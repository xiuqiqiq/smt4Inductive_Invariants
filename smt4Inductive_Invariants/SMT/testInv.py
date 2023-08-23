from z3 import *

# 创建字符串变量

n1 = String('n[1]')
n1_prime = String('n[1]\'')
x = Bool('x')
x_prime = Bool('x\'')
n2 = String('n[2]')
n2_prime = String('n[2]\'')


# 创建求解器
solver = Solver()

# 添加约束条件
solver.add(And(n1=="E"))
solver.add(And(n1_prime=="I",x_prime==True))
solver.add(n2==n2_prime)

solver.add(Not(And(n1=="C",n2=="C")))
solver.add(Not(And(n1=="C",x==True)))
solver.add(Not(And(n2=="C",x==True)))
solver.add(Not(And(n1=="E",n2=="C")))
solver.add(Not(And(n2=="E",n1=="C")))

solver.add(And(n2_prime=="E",x==True))

# solver.add(Implies(True,True))

# 检查解的存在性
print(solver.check())



# 获取模型
if solver.check() == sat:
    model = solver.model()
    print(model)
    print("n[1]=",model[n1])
    print("n[2]=",model[n2])
    print("x=",model[x])

