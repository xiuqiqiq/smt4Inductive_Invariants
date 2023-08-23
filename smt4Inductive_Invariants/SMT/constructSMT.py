import murphi
from murphiparser import *
from murphi import *
import string
import re
from itertools import combinations
import copy
import itertools



class GetSMTformula:
    def __init__(self,parse_name, node_permutations):
        self.parse_name = parse_name
        self.prot = parse_file(parse_name+".m")
        self.node_permutations = node_permutations
        self.rule_para = dict()
        self.rule_var_map = dict()
        self.inv_para = dict()
        self.inv_var_map = dict()
        self.inv_array_var_map = dict()
        self.inv_var_length = dict()
        self.inv_var_ins = dict()
        self.inv_instance = dict()
        self.rule_var_ins = dict()
        self.rule_instance = dict()
        self.ins_var = None
        self.ins_var4rule = list()
        self.ins_var_dict = dict()
        self.formula_instances = dict()

        self.deduction = dict()

        self.arrayVar_insLength = dict()

        self.booleanExpr_list = list()

        self.enum_typ_map = self.prot.enum_typ_map

        self.typ_map = self.prot.typ_map

        self.scalarsetType = self.prot.scalarset
        self.scalarsetVars = list()

        self.data_permutations = list()

    def join_statements(self,statement):
        if len(statement) == 1:
            return statement[0]
        else:
            # return (str(statement[-1]) + "& (" + self.join_statements(statement[:-1]) + ")")
            return murphi.OpExpr('&',statement[-1],self.join_statements(statement[:-1]))

    def isboolVar(self,var):
        if isinstance(var, murphi.ArrayIndex):
            # print(var.v.typ.ele_typ)
            if isinstance(var.v.typ.ele_typ, murphi.BooleanType):
                return True
        # elif isinstance(var, murphi.FieldName):
        #     print("var:", var)
        #     print(var.field)
        return False

    def getBooleanVars(self,fomula):
        if isinstance(fomula, murphi.NegExpr):
            self.getBooleanVars(fomula.expr)
        elif isinstance(fomula, murphi.OpExpr):
            if fomula.expr2 in self.booleanExpr_list and fomula.expr1 not in self.booleanExpr_list:
                self.booleanExpr_list.append(fomula.expr1)
            else:
                if isinstance(fomula.expr2, murphi.EnumValExpr) or isinstance(fomula.expr2, murphi.VarExpr):
                    pass
                elif isinstance(fomula.expr2, murphi.BooleanExpr):
                    if fomula.expr1 not in self.booleanExpr_list:
                        self.booleanExpr_list.append(fomula.expr1)
                elif self.isboolVar(fomula.expr1) or self.isboolVar(fomula.expr2):
                    if fomula.expr1 not in self.booleanExpr_list:
                        self.booleanExpr_list.append(fomula.expr1)
                    if fomula.expr2 not in self.booleanExpr_list:
                        self.booleanExpr_list.append(fomula.expr2)
                else:
                    self.getBooleanVars(fomula.expr1)
                    self.getBooleanVars(fomula.expr2)
        elif isinstance(fomula, murphi.AssignCmd):
            if fomula.expr in self.booleanExpr_list and fomula.var not in self.booleanExpr_list:
                self.booleanExpr_list.append(fomula.var)
            else:
                if isinstance(fomula.expr, murphi.EnumValExpr) or isinstance(fomula.expr, murphi.VarExpr):
                    pass
                elif isinstance(fomula.expr, murphi.BooleanExpr):
                    if fomula.var not in self.booleanExpr_list:
                        self.booleanExpr_list.append(fomula.var)
                elif self.isboolVar(fomula.var) or self.isboolVar(fomula.expr):
                    if fomula.var not in self.booleanExpr_list:
                        self.booleanExpr_list.append(fomula.var)
                    if fomula.expr not in self.booleanExpr_list:
                        self.booleanExpr_list.append(fomula.expr)
                else:
                    self.getBooleanVars(fomula.var)
                    self.getBooleanVars(fomula.expr)

    def isScalarVar(self,var):
        if isinstance(var, murphi.ArrayIndex):
            if var.v.typ.ele_typ in self.scalarsetType:
                return True
        elif isinstance(var, murphi.VarExpr):
            if str(var.typ) in self.scalarsetType:
                return True
        # elif isinstance(var, murphi.FieldName):
        #     print("var:", var)
        #     print(var.field,type(var.field))

    def getScalarsetVars(self, fomula):
        if isinstance(fomula, murphi.NegExpr):
            self.getScalarsetVars(fomula.expr)
        elif isinstance(fomula, murphi.OpExpr):
            if fomula.expr2 in self.scalarsetVars and fomula.expr1 not in self.scalarsetVars:
                self.scalarsetVars.append(fomula.expr1)
            elif fomula.expr1 in self.scalarsetVars and fomula.expr2 not in self.scalarsetVars and not str(
                    fomula.expr2).isdigit():
                self.scalarsetVars.append(fomula.expr2)
            elif fomula.expr1 in self.scalarsetVars and fomula.expr2 in self.scalarsetVars:
                pass
            else:
                if str(fomula.expr2).isdigit():
                    if fomula.expr1 not in self.scalarsetVars and not str(fomula.expr1).isdigit():
                        self.scalarsetVars.append(fomula.expr1)
                elif self.isScalarVar(fomula.expr1) or self.isScalarVar(fomula.expr2):
                    if fomula.expr1 not in self.scalarsetVars:
                        self.scalarsetVars.append(fomula.expr1)
                    if fomula.expr2 not in self.scalarsetVars:
                        self.scalarsetVars.append(fomula.expr2)
                elif isinstance(fomula.expr2, murphi.EnumValExpr) or isinstance(fomula.expr2, murphi.VarExpr):
                    pass
                else:
                    self.getScalarsetVars(fomula.expr1)
                    self.getScalarsetVars(fomula.expr2)
        elif isinstance(fomula, murphi.AssignCmd):
            if fomula.expr in self.scalarsetVars and fomula.var not in self.scalarsetVars:
                self.scalarsetVars.append(fomula.var)
            elif fomula.var in self.scalarsetVars and fomula.expr not in self.scalarsetVars and not str(
                    fomula.expr).isdigit():
                self.scalarsetVars.append(fomula.expr)
            elif fomula.var in self.scalarsetVars and fomula.expr in self.scalarsetVars:
                pass
            else:
                if str(fomula.expr).isdigit():
                    if fomula.var not in self.scalarsetVars and not str(fomula.var).isdigit():
                        self.scalarsetVars.append(fomula.var)
                elif self.isScalarVar(fomula.var) or self.isScalarVar(fomula.expr):
                    if fomula.var not in self.scalarsetVars:
                        self.scalarsetVars.append(fomula.var)
                    if fomula.expr not in self.scalarsetVars:
                        self.scalarsetVars.append(fomula.expr)
                elif isinstance(fomula.expr, murphi.EnumValExpr) or isinstance(fomula.expr, murphi.VarExpr):
                    pass
                else:
                    self.getScalarsetVars(fomula.var)
                    self.getScalarsetVars(fomula.expr)



    # Converting formulas from parameterized form to instantiated formulas
    def para2ins(self, OpExpr, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv=False):
        if isinstance(OpExpr, murphi.AssignCmd):
            if isinstance(OpExpr.expr, murphi.FieldName):
                assert isinstance(OpExpr.expr.v, murphi.ArrayIndex)
                assert isinstance(OpExpr.expr.v.idx, murphi.VarExpr)
                if OpExpr.expr.v.idx.name in inv_var_map.keys() and OpExpr.expr.v.idx.name in inv_var_ins.keys():
                    OpExpr.expr.v.idx.name = OpExpr.expr.v.idx.name.replace(OpExpr.expr.v.idx.name,
                                                                          str(inv_var_ins[OpExpr.expr.v.idx.name]))
            elif isinstance(OpExpr.expr, murphi.VarExpr):
                if OpExpr.expr.name in inv_var_map.keys() and OpExpr.expr.name in inv_var_ins.keys():
                    OpExpr.expr.name = OpExpr.expr.name.replace(OpExpr.expr.name,
                                                                      str(inv_var_ins[OpExpr.expr.name]))

            elif isinstance(OpExpr.expr, murphi.ArrayIndex):
                assert isinstance(OpExpr.expr.idx, murphi.VarExpr)
                if OpExpr.expr.idx.name in inv_var_map.keys() and OpExpr.expr.idx.name in inv_var_ins.keys():
                    OpExpr.expr.idx.name = OpExpr.expr.idx.name.replace(OpExpr.expr.idx.name,
                                                                      str(inv_var_ins[OpExpr.expr.idx.name]))

            if isinstance(OpExpr.var, murphi.ArrayIndex):
                assert isinstance(OpExpr.var.idx, murphi.VarExpr)
                if OpExpr.var.idx.name in inv_var_map.keys() and OpExpr.var.idx.name in inv_var_ins.keys():
                    OpExpr.var.idx.name = OpExpr.var.idx.name.replace(OpExpr.var.idx.name, str(inv_var_ins[OpExpr.var.idx.name]))
                    # self.ins_var4rule = OpExpr.var
                    if OpExpr.var not in self.ins_var4rule:
                        self.ins_var4rule.append(OpExpr.var)
            elif isinstance(OpExpr.var, murphi.FieldName):
                assert isinstance(OpExpr.var.v, murphi.ArrayIndex)
                assert isinstance(OpExpr.var.v.idx, murphi.VarExpr)
                if OpExpr.var.v.idx.name in inv_var_map.keys() and OpExpr.var.v.idx.name in inv_var_ins.keys():
                    OpExpr.var.v.idx.name = OpExpr.var.v.idx.name.replace(OpExpr.var.v.idx.name,
                                                                      str(inv_var_ins[OpExpr.var.v.idx.name]))
                    # self.ins_var4rule = OpExpr.var
                    if OpExpr.var not in self.ins_var4rule:
                        self.ins_var4rule.append(OpExpr.var)
            elif isinstance(OpExpr.var, murphi.VarExpr):
                # self.ins_var4rule = OpExpr.var
                if OpExpr.var not in self.ins_var4rule:
                    self.ins_var4rule.append(OpExpr.var)

        elif isinstance(OpExpr, murphi.ForallCmd):
            if OpExpr.typ in inv_var_map.values():
                expandingExpr = []
                var_length = 0
                if "node" in str(OpExpr.typ).lower():
                    var_length = self.arrayVar_insLength["node"]
                elif "data" in str(OpExpr.typ).lower():
                    var_length = self.arrayVar_insLength["data"]
                for i in range(1, var_length + 1):
                    ep_dp = copy.deepcopy(OpExpr.cmds)
                    ins_dict_ep = {str(OpExpr.var): i}
                    var_map_ep = {str(OpExpr.var): OpExpr.typ}
                    ins_ep = self.para2ins(ep_dp[0], ins_dict_ep, var_map_ep, ins_var_list2, inv_allVars_map, forinv)
                    expandingExpr.append(ins_ep)
                OpExpr = expandingExpr

        elif isinstance(OpExpr, murphi.OpExpr):
            if isinstance(OpExpr.expr1, murphi.OpExpr):
                self.para2ins(OpExpr.expr1, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
            elif isinstance(OpExpr.expr1, murphi.ArrayIndex):
                assert isinstance(OpExpr.expr1.idx, murphi.VarExpr)
                if OpExpr.expr1.idx.name in inv_var_map.keys() and OpExpr.expr1.idx.name in inv_var_ins.keys():
                    OpExpr.expr1.idx.name = OpExpr.expr1.idx.name.replace(OpExpr.expr1.idx.name,
                                                                      str(inv_var_ins[OpExpr.expr1.idx.name]))
                if OpExpr.expr1 not in ins_var_list2:
                    ins_var_list2.append(OpExpr.expr1)
                if forinv:
                    self.ins_var = ins_var_list2
            elif isinstance(OpExpr.expr1, murphi.VarExpr):
                if OpExpr.expr1.name in inv_var_map.keys() and OpExpr.expr1.name in inv_var_ins.keys():
                    OpExpr.expr1.name = OpExpr.expr1.name.replace(OpExpr.expr1.name, str(inv_var_ins[OpExpr.expr1.name]))
                elif OpExpr.expr1.name in inv_allVars_map.keys():
                    if OpExpr.expr1 not in ins_var_list2:
                        ins_var_list2.append(OpExpr.expr1)
                    if forinv:
                        self.ins_var = ins_var_list2
            elif isinstance(OpExpr.expr1, murphi.FieldName):
                # print("出现FieldName类型：", OpExpr.expr1)
                # print(OpExpr.expr1)
                # print("OpExpr.expr1.v-1:",OpExpr.expr1.v)
                assert isinstance(OpExpr.expr1.v, murphi.ArrayIndex)
                assert isinstance(OpExpr.expr1.v.idx, murphi.VarExpr)
                if OpExpr.expr1.v.idx.name in inv_var_map.keys() and OpExpr.expr1.v.idx.name in inv_var_ins.keys():
                    OpExpr.expr1.v.idx.name = OpExpr.expr1.v.idx.name.replace(OpExpr.expr1.v.idx.name,
                                                                      str(inv_var_ins[OpExpr.expr1.v.idx.name]))
                if OpExpr.expr1 not in ins_var_list2:
                    ins_var_list2.append(OpExpr.expr1)
                if forinv:
                    self.ins_var = ins_var_list2
            elif isinstance(OpExpr.expr1, murphi.ForallExpr):
                if OpExpr.expr1.typ in inv_var_map.values():
                    expandingExpr = []
                    var_length = 0
                    if "node" in str(OpExpr.expr1.typ).lower():
                        var_length = self.arrayVar_insLength["node"]
                    elif "data" in str(OpExpr.expr1.typ).lower():
                        var_length = self.arrayVar_insLength["data"]
                    for i in range(1, var_length + 1):
                        ep1_dp = copy.deepcopy(OpExpr.expr1.expr)
                        ins_dict_ep1 = {str(OpExpr.expr1.var): i}
                        var_map_ep1 = {str(OpExpr.expr1.var): OpExpr.expr1.typ}
                        ins_ep1 = self.para2ins(ep1_dp, ins_dict_ep1, var_map_ep1, ins_var_list2, inv_allVars_map, forinv)
                        expandingExpr.append(ins_ep1)
                    join_statements = self.join_statements(expandingExpr)
                    OpExpr.expr1 = join_statements
            else:
                pass

            if isinstance(OpExpr.expr2, murphi.OpExpr):
                self.para2ins(OpExpr.expr2, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
            elif isinstance(OpExpr.expr2, murphi.VarExpr):
                # print("inv_var_ins:",inv_var_ins)
                if OpExpr.expr2.name in inv_var_map.keys() and OpExpr.expr2.name in inv_var_ins.keys():
                    OpExpr.expr2.name = OpExpr.expr2.name.replace(OpExpr.expr2.name, str(inv_var_ins[OpExpr.expr2.name]))
                elif OpExpr.expr2.name in inv_allVars_map.keys():
                    if OpExpr.expr2 not in ins_var_list2:
                        ins_var_list2.append(OpExpr.expr2)
                    if forinv:
                        self.ins_var = ins_var_list2
            elif isinstance(OpExpr.expr2, murphi.ForallExpr):
                if OpExpr.expr2.typ in inv_var_map.values():
                    expandingExpr = []
                    var_length = 0
                    if "node" in str(OpExpr.expr2.typ).lower():
                        var_length = self.arrayVar_insLength["node"]
                    elif "data" in str(OpExpr.expr2.typ).lower():
                        var_length = self.arrayVar_insLength["data"]
                    for i in range(1,var_length+1):
                        ep2_dp = copy.deepcopy(OpExpr.expr2.expr)
                        ins_dict_ep2 = {str(OpExpr.expr2.var):i}
                        var_map_ep2 = {str(OpExpr.expr2.var):OpExpr.expr2.typ}
                        ins_ep2 = self.para2ins(ep2_dp, ins_dict_ep2, var_map_ep2, ins_var_list2, inv_allVars_map, forinv)
                        expandingExpr.append(ins_ep2)
                    join_statements = self.join_statements(expandingExpr)
                    OpExpr.expr2 = join_statements
            else:
                pass

        elif isinstance(OpExpr, murphi.NegExpr):
            self.para2ins(OpExpr.expr, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)

        return OpExpr

    def getRules(self):

        sub_rule_ins = dict()
        for name, rule in self.prot.rule_map.items():
            # print(name)
            sub_rule_dict = dict()
            # for var: name and type
            sub_rule_dict["var"] = rule.var_map
            self.rule_var_map[name] = rule.var_map
            # for guard: OpExpr
            sub_rule_dict["guard"] = rule.rule.cond
            # for assignments
            sub_rule_dict["assign"] = rule.rule.cmds
            self.rule_para[name] = sub_rule_dict
            # print(self.rule_para)
            # for construct instantiated rule vars
            # m:不变式参数个数 的n:规则的参数个数 排列
            # print("self.inv_var_map:",self.inv_var_map, self.inv_var_length)
            inv_name=""

            sub_var_ins = dict()
            for inv in self.inv_var_length.keys():
                inv_name = inv
                permutations = [(1,),(2,)]

                # 实例化
                # node_permutations = [1,2]
                self.data_permutations = [1,2]

                self.arrayVar_insLength["node"] = len(self.node_permutations)
                self.arrayVar_insLength["data"] = len(self.data_permutations)
                for var,type in sub_rule_dict["var"].items():
                    assert isinstance(type, murphi.VarType)
                    # 规则中的参数与不变式中的参数一致
                    if "node" in type.name.lower():
                        sub_var_ins[var] = self.node_permutations
                    elif "data" in type.name.lower():
                        sub_var_ins[var] = self.data_permutations

            sub_rule_ins[name] = sub_var_ins
            self.rule_var_ins[inv_name] = sub_rule_ins
            # print(self.rule_var_ins[inv_name])
        # print("self.rule_var_ins:",self.rule_var_ins)

        # print("rule_var_ins:",self.rule_var_ins)
        # for inv:all rules
        for inv,rules in self.rule_var_ins.items():
            # print("inv:",inv)
            rule_vars_dict = dict()
            # for inv-one rule:instantiated rule vars
            for rule,rule_vars in rules.items():
                # print("rule:",rule)
                # print("rule_vars:",rule_vars)
                # for each var
                i = 1

                ins_permutations = list(itertools.product(*rule_vars.values()))
                ins_permutations = [{key: value for key, value in zip(rule_vars.keys(), combo)} for combo in ins_permutations]
                # print("ins_permutation:",ins_permutations)
                for ins_permutation in ins_permutations:
                    sub_rule_instance_dict = dict()
                    ins_var4rule_list = list()
                    instance_name = inv + "_" + rule + str(i)

                    ins_dict = ins_permutation
                    # for guard
                    guard_dp = copy.deepcopy(self.rule_para[rule]["guard"])
                    sub_rule_instance_dict["guard"] = self.para2ins(guard_dp, ins_dict, self.rule_var_map[rule], [], {})
                    self.getBooleanVars(sub_rule_instance_dict["guard"])
                    self.getScalarsetVars(sub_rule_instance_dict["guard"])

                    # for assignment
                    sub_assign_list = list()
                    for assignment in self.rule_para[rule]["assign"]:
                        # print(inv, rule, assignment, ins_dict)
                        assign_dp = copy.deepcopy(assignment)
                        self.ins_var4rule = list()
                        if isinstance(assignment, murphi.UndefineCmd):
                            pass
                        else:
                            assignCmds = self.para2ins(assign_dp, ins_dict, self.rule_var_map[rule], [], {})

                            if isinstance(assignCmds, list):
                                sub_assign_list.extend(assignCmds)
                                for assignCmd in assignCmds:
                                    self.getBooleanVars(assignCmd)
                                    self.getScalarsetVars(assignCmd)
                            else:
                                self.getBooleanVars(assignCmds)
                                self.getScalarsetVars(assignCmds)
                                sub_assign_list.append(assignCmds)
                        if self.ins_var4rule:
                            # ins_var4rule_list.append(self.ins_var4rule)
                            ins_var4rule_list.extend(self.ins_var4rule)
                    assign_vars = ins_var4rule_list

                    sub_rule_instance_dict["assign"] = sub_assign_list
                    sub_rule_instance_dict["assumption"] = [elem for elem in self.ins_var_dict[inv] if
                                                            elem not in ins_var4rule_list]
                    sub_rule_instance_dict["!inv"] = murphi.NegExpr(self.inv_instance[inv])

                    print(instance_name, sub_rule_instance_dict)
                    # self.formula_instances[instance_name] = sub_rule_instance_dict

                    # using invHoldForRule2 from paraverifier
                    if self.invHoldForRule2(assign_vars, self.ins_var_dict[inv]):
                        self.formula_instances[instance_name] = sub_rule_instance_dict
                    else:
                        self.deduction[instance_name] = sub_rule_instance_dict

                    i += 1



        # print("有效F:",self.formula_instances)
        # print("无效F:",self.deduction)
        print("booleanExpr_list:", self.booleanExpr_list)
        print("scalarsetVars:", self.scalarsetVars)
        # 打开文件并写入内容
        with open(self.parse_name+'_formula.txt', 'w') as file:
            file.write("\n\n")
            file.write("All parameterized rules:\n")
            file.write(str(self.rule_para))
            file.write("\n\n")
            file.write("All parameterized invariants:\n")
            file.write(str(self.inv_para))
            file.write("\n\n")
            file.write("All instantiated invariants:\n")
            file.write(str(self.inv_instance))
            file.write("\n\n")
            file.write("Invalid F:\n")
            file.write(str(self.deduction))
            file.write("\n\n")
            file.write("Valid F:\n")
            file.write(str(self.formula_instances))
            file.write("\n\n")

    def invHoldForRule2(self,assignVars,invVars):
        for invVar in invVars:
            for assignVar in assignVars:
                if invVar == assignVar:
                    return True
        return False


    def getInvVars(self, inv, inv_name, sub_var_dict, sub_inv_dict, sub_array_var):
        if isinstance(inv, murphi.ForallExpr):
            sub_var_dict[inv.var] = inv.typ
            sub_array_var[inv.var] = inv.typ
            if isinstance(inv.expr, murphi.ForallExpr):
                self.getInvVars(inv.expr, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)
            else:
                self.getInvVars(inv.expr, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)
                sub_inv_dict["invs"] = inv.expr
        elif isinstance(inv, murphi.VarExpr):
            sub_var_dict[inv.name] = inv.typ

        elif isinstance(inv, murphi.OpExpr):
            if isinstance(inv.expr1,murphi.ForallExpr) | isinstance(inv.expr2, murphi.ForallExpr):
                if isinstance(inv.expr1, murphi.ForallExpr):
                    _, half_inv,_ = self.getInvVars(inv.expr1, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)
                    sub_inv_dict["invs"] = murphi.OpExpr(inv.op, half_inv["invs"], inv.expr2)
                elif isinstance(inv.expr1, murphi.OpExpr):
                    self.getInvVars(inv.expr1.expr1, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)
                    self.getInvVars(inv.expr1.expr2, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)
                if isinstance(inv.expr2, murphi.ForallExpr):
                    _, half_inv,_ = self.getInvVars(inv.expr2, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)
                    sub_inv_dict["invs"] = murphi.OpExpr(inv.op, inv.expr1, half_inv["invs"])
                elif isinstance(inv.expr2, murphi.OpExpr):
                    self.getInvVars(inv.expr2.expr1, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)
                    self.getInvVars(inv.expr2.expr2, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)
            else:
                self.getInvVars(inv.expr1, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)
                self.getInvVars(inv.expr2, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)

            # sub_inv_dict["invs"] = inv

        elif isinstance(inv, murphi.NegExpr):
            self.getInvVars(inv.expr, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)

        return sub_var_dict, sub_inv_dict, sub_array_var


    def getInvs(self):
        inv_name = ""
        for inv in self.prot.inv_map.values():
            inv_name = inv.name
            # print("inv_name:",inv_name)
            assert isinstance(inv, MurphiInvariant)
            # print("inv.inv:",inv.inv)
            # for var: name and type
            sub_var_dict, sub_inv_dict, sub_array_var = self.getInvVars(inv.inv, inv_name, {}, {}, {})
            sub_inv_dict["var"] = sub_var_dict
            self.inv_var_map[inv_name] = sub_var_dict
            self.inv_array_var_map[inv_name] = sub_array_var
            self.inv_var_length[inv_name] = len(sub_var_dict)
            # print("self.inv_var_map:", self.inv_var_map)
            # print("self.inv_array_var_map:",self.inv_array_var_map)
            self.inv_para[inv_name] = sub_inv_dict
            # print("self.inv_para:", self.inv_para)


        # instances for parameters
            inv_insNum = 1
            sub_insVar = dict()
            # 带参形式的实例化
            for var in sub_array_var.keys():
                sub_insVar[var] = inv_insNum
                inv_insNum +=1
            self.inv_var_ins[inv_name] = sub_insVar
            # print(self.inv_var_ins)
            # print(self.inv_para[inv_name]["invs"], self.inv_var_ins[inv_name])
            dp = copy.deepcopy(self.inv_para[inv_name]["invs"])
            # print(dp)
            self.ins_var = None
            # print("self.inv_var_ins[inv_name]:",self.inv_var_ins[inv_name])
            self.inv_instance[inv_name] = self.para2ins(dp, self.inv_var_ins[inv_name],self.inv_array_var_map[inv_name],[],self.inv_var_map[inv_name],True)
            # print("self.inv_instance:",self.inv_instance)
            if not self.ins_var==None:
                ins_var = copy.deepcopy(self.ins_var)
                self.ins_var_dict[inv_name] = ins_var
            # print(self.inv_para[inv_name]["invs"],self.inv_var_ins[inv_name])
            # {'mutualEx': OpExpr(->, 1 != 2, n[1] = C ->   n[2] != C)}
            # print("self.ins_var_dict:", self.ins_var_dict)
            self.getBooleanVars(self.inv_instance[inv_name])
            self.getScalarsetVars(self.inv_instance[inv_name])
            # print("self.booleanExpr_list:",self.booleanExpr_list)
            self.getRules()

if __name__ == "__main__":
    # parse_name = "../protocols/mutualEx/mutualEx"
    parse_name = "protocols/mutdata/mutdata"
    # parse_name = "../protocols/german/german"
    # parse_name = "../protocols/german_withoutData/german_withoutData"
    # GetSMTformula(parse_name=parse_name).getRules()
    GetSMTformula(parse_name=parse_name, node_permutations=[1,2]).getInvs()
