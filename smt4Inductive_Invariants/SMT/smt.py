import murphi
import constructSMT
from z3 import *
import itertools
import subprocess
import re

class ConstructF():
    def __init__(self,name,instance,inv_path):
        self.name = name
        self.inv_path = inv_path

        self.guard = instance["guard"]
        assert isinstance(self.guard,murphi.OpExpr)

        self.assign = instance["assign"]
        assert all(isinstance(f, murphi.AssignCmd) for f in self.assign)

        self.assumption = instance["assumption"]

        self.negInv = instance["!inv"]

        self.pmurphi = dict()


        self.variables = dict()
        self.boundStates = list()

        self.aux_inv = list()

    def getVars(self,fomula,vardict,replacement=""):
        # for guard's & negInv's variables
        if isinstance(fomula, murphi.OpExpr):
            if fomula.op=='->':
                print("fomula->:",fomula)
                # to CNF
                cnf = murphi.NegExpr(murphi.OpExpr('&',fomula.expr1,murphi.NegExpr(fomula.expr2)))
                self.getVars(cnf,vardict,replacement)
                print("cnf:",cnf)
                # ex1 = self.getVars(fomula.expr1, vardict, replacement)
                # print("ex1:",ex1,fomula.expr1,vardict)
                # if ex1==True:
                #     ex2 = self.getVars(fomula.expr2, vardict, replacement)
                #     print("ex2T:", ex2, fomula.expr2, vardict)
                # else:
                #     ex2 = self.getVars(fomula.expr2, vardict, replacement)
                #     print("ex2F:", ex2, fomula.expr2, vardict)
                    # a = Implies()

            if isinstance(fomula.expr1, murphi.OpExpr):
                self.getVars(fomula.expr1, vardict, replacement)
            elif isinstance(fomula.expr1, murphi.ArrayIndex):
                assert isinstance(fomula.expr1.idx, murphi.VarExpr)
                # if str(fomula.expr1)+replacement not in vardict.keys():
                if isinstance(fomula.expr2, murphi.BooleanExpr):
                    if str(fomula.expr1) + replacement not in vardict.keys():
                        if replacement=="":
                            vardict[str(fomula.expr1) + replacement] = [Bool(str(fomula.expr1) + replacement),fomula.expr1]
                        else:
                            vardict[str(fomula.expr1)+replacement] = [Bool(str(fomula.expr1)+replacement)]
                else:
                    if str(fomula.expr1) + replacement not in vardict.keys():
                        if replacement == "":
                            vardict[str(fomula.expr1) + replacement] = [String(str(fomula.expr1) + replacement),fomula.expr1]
                        else:
                            vardict[str(fomula.expr1)+replacement] = [String(str(fomula.expr1)+replacement)]
                    if isinstance(fomula.expr2,murphi.EnumValExpr):
                        self.pmurphi[str(fomula.expr2)] = fomula.expr2
                        if fomula.op == '=':
                            self.boundStates.append(vardict[str(fomula.expr1)+replacement][0] == str(fomula.expr2))
                        elif fomula.op == '!=':
                            self.boundStates.append(vardict[str(fomula.expr1) + replacement][0] != str(fomula.expr2))
            elif isinstance(fomula.expr1, murphi.VarExpr):
                if (fomula.expr1.name).isdigit() and isinstance(fomula.expr2, murphi.VarExpr) and (fomula.expr2.name).isdigit():
                    # print(fomula)
                    pass
                    # return True
                else:
                    # if str(fomula.expr1)+replacement not in vardict.keys():
                    if isinstance(fomula.expr2, murphi.BooleanExpr):
                        # print(fomula.expr1, fomula.expr2, type(fomula.expr2))
                        if str(fomula.expr1) + replacement not in vardict.keys():
                            if replacement=="":
                                vardict[str(fomula.expr1) + replacement] = [Bool(str(fomula.expr1) + replacement),fomula.expr1]
                            else:
                                vardict[str(fomula.expr1)+replacement] = Bool(str(fomula.expr1)+replacement)
                        boolValue = True if fomula.expr2.val else False
                        self.pmurphi[str(boolValue)] = fomula.expr2
                        if fomula.op == '=':
                            self.boundStates.append(vardict[str(fomula.expr1)+replacement][0] == boolValue)
                    else:
                        if str(fomula.expr1) + replacement not in vardict.keys():
                            if replacement=="":
                                vardict[str(fomula.expr1) + replacement] = [String(str(fomula.expr1) + replacement),fomula.expr1]
                            else:
                                vardict[str(fomula.expr1)+replacement] = String(str(fomula.expr1)+replacement)
            else:
                pass

            if isinstance(fomula.expr2, murphi.OpExpr) | isinstance(fomula.expr2, murphi.NegExpr):
                self.getVars(fomula.expr2, vardict, replacement)
            elif isinstance(fomula.expr2, murphi.ArrayIndex):
                assert isinstance(fomula.expr2.idx, murphi.VarExpr)
                # if str(fomula.expr1)+replacement not in vardict.keys():
                if isinstance(fomula.expr1, murphi.BooleanExpr):
                    if str(fomula.expr2) + replacement not in vardict.keys():
                        if replacement=="":
                            vardict[str(fomula.expr2) + replacement] = [Bool(str(fomula.expr2) + replacement),fomula.expr2]
                        else:
                            vardict[str(fomula.expr2)+replacement] = Bool(str(fomula.expr2)+replacement)
                else:
                    if str(fomula.expr2) + replacement not in vardict.keys():
                        if replacement=="":
                            vardict[str(fomula.expr2) + replacement] = [String(str(fomula.expr2) + replacement),fomula.expr2]
                        else:
                            vardict[str(fomula.expr2)+replacement] = String(str(fomula.expr2)+replacement)
                    if isinstance(fomula.expr1,murphi.EnumValExpr):
                        self.pmurphi[str(fomula.expr1)] = fomula.expr1
                        if fomula.op == '=':
                            self.boundStates.append(vardict[str(fomula.expr2)+replacement][0] == str(fomula.expr1))
                        elif fomula.op == '!=':
                            self.boundStates.append(vardict[str(fomula.expr2) + replacement][0] != str(fomula.expr1))
            elif isinstance(fomula.expr2, murphi.VarExpr):
                if (fomula.expr2.name).isdigit() and isinstance(fomula.expr1, murphi.VarExpr) and (fomula.expr1.name).isdigit():
                    # print(fomula)
                    pass
                    # return True
                else:
                    # if str(fomula.expr1)+replacement not in vardict.keys():
                    if isinstance(fomula.expr1, murphi.BooleanExpr):
                        # print(fomula.expr1, fomula.expr2, type(fomula.expr2))
                        if str(fomula.expr2) + replacement not in vardict.keys():
                            if replacement=="":
                                vardict[str(fomula.expr2) + replacement] = [Bool(str(fomula.expr2) + replacement),fomula.expr2]
                            else:
                                vardict[str(fomula.expr2)+replacement] = Bool(str(fomula.expr2)+replacement)
                        boolValue = True if fomula.expr1.val else False
                        self.pmurphi[str(boolValue)] = fomula.expr1
                        if fomula.op == '=':
                            self.boundStates.append(vardict[str(fomula.expr2)+replacement][0] == boolValue)
                    else:
                        if str(fomula.expr2) + replacement not in vardict.keys():
                            if replacement=="":
                                vardict[str(fomula.expr2) + replacement] = [String(str(fomula.expr2) + replacement),fomula.expr2]
                            else:
                                vardict[str(fomula.expr2)+replacement] = [String(str(fomula.expr2)+replacement)]
            # elif isinstance(fomula.expr2, murphi.NegExpr):
            #     print("neg:",fomula.expr2)
            else:
                pass

        # for assign's variables
        if isinstance(fomula, murphi.AssignCmd):
            # print("fomula:",fomula,fomula.var,fomula.expr)
            if str(fomula.var)+"'" not in vardict.keys():
                if isinstance(fomula.expr, murphi.BooleanExpr):
                    vardict[str(fomula.var)+"'"] = [Bool(str(fomula.var)+"'")]
                    boolValue = True if fomula.expr.val else False
                    self.pmurphi[str(boolValue)] = fomula.expr
                    self.boundStates.append(vardict[str(fomula.var)+"'"][0] == boolValue)
                else:
                    vardict[str(fomula.var)+"'"] = [String(str(fomula.var)+"'")]
                    if isinstance(fomula.expr,murphi.EnumValExpr):
                        self.pmurphi[str(fomula.expr)] = fomula.expr
                        self.boundStates.append(vardict[str(fomula.var)+"'"][0] == str(fomula.expr))

        # for !inv's variables
        if isinstance(fomula, murphi.NegExpr):
            if isinstance(fomula.expr, murphi.OpExpr):
                if fomula.expr.op == '->':
                    # print("fomula.expr->:", fomula.expr)
                    # to CNF
                    cnf = murphi.OpExpr('&', fomula.expr.expr1, murphi.NegExpr(fomula.expr.expr2))
                    self.getVars(cnf, vardict, replacement)
                    # print("cnf:", cnf)
                if fomula.expr.op == '!=':
                    self.getVars(murphi.OpExpr('=',fomula.expr.expr1,fomula.expr.expr2), vardict, replacement)

                # print(fomula.expr)
                # self.getVars(fomula.expr, vardict,replacement)

        return vardict

    def join_statements(self,statement):
        if len(statement) == 1:
            return statement[0]
        else:
            # return (str(statement[-1]) + "& (" + self.join_statements(statement[:-1]) + ")")
            return murphi.OpExpr('&',statement[-1],self.join_statements(statement[:-1]))

    def smtFormula(self):
        solve = Solver()

        # variables
        # for guard's variables
        self.variables = self.getVars(self.guard,{})
        # print("states after guard:",self.boundStates)
        # print("for guard's variables:",self.variables)
        # for assign's variables
        for assign in self.assign:
            self.variables = self.getVars(assign, self.variables)
        # print("for guard's+assign's variables:",self.variables)
        # print("states after assign:",self.boundStates)
        # for !inv's variables
        invdict = dict()
        inv2dict = dict()
        self.variables = self.getVars(self.negInv, self.variables, "'")
        # print("self.negInv:",self.negInv)
        # print("states after inv:", self.boundStates)
        # print("after !inv:",self.variables)
        # invdict = self.getVars(self.negInv, invdict, "'")
        # print("invdict_before:",invdict)
        # for key in invdict.keys():
        #     if key+"'" not in self.variables.keys():
        #         self.variables[key+"'"] = invdict[key]
        # print("invdict_after:",self.variables)

        # for assumption's variables

        # for assumption's variables
        for assumption in self.assumption:
            if str(assumption) not in self.variables.keys():
                # print("assumption:",assumption)
                self.variables[str(assumption)] = [String(str(assumption)),assumption]
            if str(assumption)+"'" not in self.variables.keys():
                # print("assumption:", assumption+"'")
                self.variables[str(assumption)+"'"] = [String(str(assumption)+"'")]
            self.boundStates.append(self.variables[str(assumption)][0] == self.variables[str(assumption)+"'"][0])

        # print("states after assumption:", self.boundStates)
        # print("assumption_after:", self.variables)
        # print("pmurphi:",self.pmurphi)

        cti = {k: v for k, v in self.variables.items() if not k.endswith("'")}

        for state in self.boundStates:
            # print(state)
            solve.add(state)
        # print(solve.check())
        if solve.check() == sat:
            model = solve.model()
            print("解是：\n")
            print(model)
            inv_list = list()
            for k,v in cti.items():
                value=""
                if isinstance(model[v[0]],SeqRef):
                    # value = model[v[0]].as_string()

                    # Manual adjustment for aux1
                    if model[v[0]].as_string()=="T":
                        value = model[v[0]].as_string()
                    else:
                        value = model[v[0]].as_string()
                elif isinstance(model[v[0]],BoolRef):
                    value = str(is_true(model[v[0]]))
                # print("murphi表示:",murphi.OpExpr('=',v[1],self.pmurphi[value]))
                if value != "":
                    inv_list.append(murphi.OpExpr('=', v[1], self.pmurphi[value]))
                # inv_list.append(f"{v[0]} == {model[v[0]]}")
            print("invlist:",inv_list)
            self.call_LS(inv_list)
            print("self.aux_inv:",self.aux_inv)
            # new_inv = f"invariant \"{self.name}\"\n {murphi.indent(str(self.aux_inv),2)};"
            # print(f"invariant '{self.name}'")
            # print(new_inv)
            # print("\n")
            with open(self.inv_path+"_invs.txt","a") as file:
                file.write(f"invariant '{self.name}'\n")
                file.write(murphi.indent(str(self.aux_inv),2))
                file.write(";\n")
            # print("Old c.inv_instance:", c.inv_instance)
            # c.inv_instance[self.name] = new_inv
            # print("New c.inv_instance:", c.inv_instance)

    def call_LS(self, inv_list):
        print("inv_list",inv_list)
        counter_ex,can_inv = self.call_cmurphi(inv_list)
        if not counter_ex:
            self.aux_inv = can_inv
            if len(inv_list)>1:
                for sublist in self.get_sublists(inv_list, len(inv_list)-1):
                    print("sublist:",sublist)
                    if self.call_LS(sublist):
                        break
            return True
        else:
            return False
        # sub_list = self.get_sublists(inv_list, len(inv_list)-1)

    def call_cmurphi(self, inv_list):
        can_inv = murphi.NegExpr(self.join_statements(inv_list))
        # print(f"invariant '{self.name}'\n {murphi.indent(str(can_inv),2)};")
        new_inv = f"invariant \"{self.name}\"\n {murphi.indent(str(can_inv),2)};"
        print("new_inv:",new_inv)
        self.appendInv_and_save(self.inv_path+"_withoutInv.m", new_inv, self.inv_path+"_newTmp.m")

        cmurphi_path = '../../cmurphi_LS'
        # file = '../protocols/mutualEx/mutualEx.m'
        file = self.inv_path
        # print("file:",file)
        process1 = subprocess.Popen("{0}/src/mu {1}_newTmp.m".format(cmurphi_path, file), shell=True,
                                    stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE)
        (stdout, stderr) = process1.communicate()
        if not re.search(r'Code generated', stdout.decode('utf-8')):
            raise ValueError

        command2 = "g++ -ggdb -o {0}_newTmp.o {0}_newTmp.cpp -I {1}/include -lm".format(file, cmurphi_path)
        process2 = subprocess.Popen(command2, shell=True,
                                    stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE)
        process2.communicate()
        if not os.path.exists("./{0}_newTmp.o".format(file)): raise FileExistsError

        process3 = subprocess.Popen("./{0}_newTmp.o -localsearch -m 5000".format(file), shell=True,
                                    stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE)

        (stdoutdata, stderrdata) = process3.communicate()
        pattern_counter = re.compile(r'Invariant\s"(\w+).*"\sfailed')
        counter_ex = re.findall(pattern_counter, stdoutdata.decode('utf-8'))

        os.remove('%s_newTmp.cpp' % file)
        os.remove('%s_newTmp.o' % file)
        # os.remove('%s_newTmp.m' % file)
        if not counter_ex:
            print('No cti found. The invariants are OK.')
            return False,can_inv
        else:
            print('counter_ex:', counter_ex)
            return True,can_inv

    def appendInv_and_save(self, file_path, new_inv, new_file_path):
        with open(file_path, 'r') as file:
            content = file.read()

        updated_protocol = content + new_inv

        with open(new_file_path, 'w') as new_file:
            new_file.write(updated_protocol)

    def get_sublists(self, lst, sublist_length):
        sublists = list(itertools.combinations(lst, sublist_length))
        sublists = [list(sublist) for sublist in sublists]  # 转换为列表形式
        return sublists

if __name__ == "__main__":
    parse_name = "../protocols/mutualEx/mutualEx"
    # inv_path = parse_name+"_invs.txt"
    inv_path = parse_name
    # inv_file = open(inv_path, "w")
    # GetSMTformula(parse_name=parse_name).getRules()
    c = constructSMT.GetSMTformula(parse_name=parse_name)
    c.getInvs()
    print(c.formula_instances)

    # old instance的值deepcope一份
    for name,instance in c.formula_instances.items():
        # print(instance)
        # 先把inv_instance清空
        ConstructF(name,instance,inv_path).smtFormula()
        # 做完smt check之后，如果发现inv_instance为空了，那么说明已经没有更多反例，已找到归纳不变式
        # 如果inv_instance不为空，那么说明有反例，需要构造新的formula_instances



