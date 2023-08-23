import murphi
import constructSMT
from z3 import *
import itertools
import subprocess
import re
from collections import defaultdict
import shutil
from murphiparser import *

import sys
import time

log_print = open('record.log', 'w')
sys.stdout = log_print
sys.stderr = log_print



callSmt = 0
callLS = 0
invPattern = list()
invPattern_dict = dict()
enum_value_map = dict()
invlist_dict = dict()



class ConstructF():
    def __init__(self,name,instance,inv_path,ori_inv,boolVars,enum_typ_map,typ_map,scalarsetVars,data_permutations):
        self.name = name
        self.inv_path = inv_path
        self.ori_inv = ori_inv
        self.boolVars = boolVars

        self.guard = instance["guard"]
        assert isinstance(self.guard,murphi.OpExpr)

        self.assign = instance["assign"]
        assert all(isinstance(f, murphi.AssignCmd) for f in self.assign)

        self.assumption = instance["assumption"]

        self.negInv = instance["!inv"]

        # self.inv = instance["inv"]

        self.pmurphi = dict()

        self.variables = dict()
        self.boundStates = list()

        self.solver = Solver()

        self.aux_inv = None


        self.enum_typ_map = enum_typ_map
        self.enum_vars = dict()

        self.enum_notEqulVars = list()
        self.enum_notEqulVars_map = dict()
        self.enum_EqulVars = list()

        self.typ_map = typ_map

        self.paraVars = list()
        self.var_list = []

        self.murphiInvLines = ""

        self.scalarsetVars = scalarsetVars

        self.data_permutations = data_permutations
        self.dataVars = []


    def defEnum(self):
        for enum_typ,enum_value in self.enum_typ_map.items():
            if enum_typ in enum_value_map.keys():
                pass
            else:
                assert isinstance(enum_value, murphi.EnumType)
                sub_enumValue = dict()
                enumDef = ""
                valueDef = []
                sub_enumValue[enum_typ] = z3.DatatypeSortRef
                for index, name in enumerate(enum_value.names):
                    sub_enumValue[name] = z3.DatatypeRef
                    if index == len(enum_value.names) - 1:
                        enumDef = enumDef + f"sub_enumValue[\"{name}\"]"
                    else:
                        enumDef = enumDef + f"sub_enumValue[\"{name}\"], "
                    valueDef.append(name)
                # like enumType["CACHE_STATE"],(enumValue["I"], enumValue["S"], enumValue["E"]) = EnumSort('CACHE_STATE',['I', 'S', 'E'])
                exec_line = "sub_enumValue[enum_typ], " + "(" + enumDef + ")" +"=" + "EnumSort" + "(enum_typ, valueDef)"
                exec(exec_line)
                enum_value_map[enum_typ] = sub_enumValue


    def isdigit(self,fomula):
        assert isinstance(fomula, murphi.OpExpr)
        if isinstance(fomula.expr1, murphi.OpExpr):
            if self.isdigit(fomula.expr1)==False:
                return False
        if isinstance(fomula.expr2, murphi.OpExpr):
            if self.isdigit(fomula.expr2)==False:
                return False
        if isinstance(fomula.expr1, murphi.VarExpr) and (fomula.expr1.name).isdigit() and isinstance(fomula.expr2, murphi.VarExpr) and (fomula.expr2.name).isdigit():
            return True
        else:
            return False

    def smtOP(self,expr1,expr2,op):
        if op == '=':
            if str(expr1) in self.enum_vars and str(expr2) in enum_value_map[self.enum_vars[str(expr1)]]:
                if str(expr1) not in self.enum_EqulVars and not str(expr1).endswith('\''):
                    self.enum_EqulVars.append(str(expr1))
                return expr1 == enum_value_map[self.enum_vars[str(expr1)]][expr2]

            return expr1 == expr2
        if op == '!=':
            if str(expr1) in self.enum_vars and str(expr2) in enum_value_map[self.enum_vars[str(expr1)]]:
                if str(expr1) not in self.enum_notEqulVars and not str(expr1).endswith('\''):
                    self.enum_notEqulVars.append(str(expr1))
                if not str(expr1).endswith('\'') and str(expr1) in self.enum_notEqulVars_map.keys():
                    self.enum_notEqulVars_map[str(expr1)].append(str(expr2))
                elif not str(expr1).endswith('\''):
                    self.enum_notEqulVars_map[str(expr1)] = [str(expr2)]
                return expr1 != enum_value_map[self.enum_vars[str(expr1)]][expr2]
            return expr1 != expr2
        if op == '&':
            return And(expr1,expr2)
        if op == '|':
            return Or(expr1,expr2)
        if op == '->':
            return Implies(expr1,expr2)

    def getVal(self,expr):
        if isinstance(expr, murphi.EnumValExpr):
            return str(expr.enum_val)
        elif isinstance(expr, murphi.BooleanExpr):
            return True if expr.val else False
        elif str(expr).isdigit():
            return int(str(expr))
        else:
            return str(expr)

    def setKey(self, expr, replacement, isbool=False, isdigit=False):
        if isbool:
            if replacement == "":
                return [Bool(str(expr) + replacement), expr]
            else:
                return [Bool(str(expr) + replacement)]
        elif isdigit:
            self.dataVars.append(str(expr) + replacement)
            if replacement == "":
                return [Int(str(expr) + replacement), expr]
            else:
                return [Int(str(expr) + replacement)]
        elif isinstance(expr, murphi.ArrayIndex):
            if expr.v.typ.ele_typ.name in enum_value_map:
                # self.enum_vars[str(expr)] = Const(str(expr),enum_value_map[expr.v.typ.ele_typ.name][expr.v.typ.ele_typ.name])
                self.enum_vars[str(expr) + replacement] = expr.v.typ.ele_typ.name
                #             self.solver.add(self.enum_vars[str(expr)] != enum_value_map[expr.v.typ.ele_typ.name]["I"])
                if replacement == "":
                    return [Const(str(expr) + replacement,
                                  enum_value_map[expr.v.typ.ele_typ.name][expr.v.typ.ele_typ.name]), expr]
                else:
                    return [Const(str(expr) + replacement,
                                  enum_value_map[expr.v.typ.ele_typ.name][expr.v.typ.ele_typ.name])]
            else:
                if replacement == "":
                    return [z3.String(str(expr) + replacement), expr]
                else:
                    return [z3.String(str(expr) + replacement)]

        elif isinstance(expr, murphi.FieldName):
            isEnum = False
            enum_name = ""
            for typ_decl in self.typ_map[expr.v.v.typ.ele_typ.name].typ_decls:
                assert isinstance(typ_decl, murphi.MurphiTypeDecl)
                if str(expr.field) == typ_decl.name:
                    if typ_decl.typ.name in enum_value_map:
                        enum_name = typ_decl.typ.name
                        isEnum = True
            if isEnum:
                self.enum_vars[str(expr) + replacement] = enum_name

                if replacement == "":
                    return [Const(str(expr) + replacement, enum_value_map[enum_name][enum_name]), expr]
                else:
                    return [Const(str(expr) + replacement, enum_value_map[enum_name][enum_name])]
            else:
                if replacement == "":
                    return [z3.String(str(expr) + replacement), expr]
                else:
                    return [z3.String(str(expr) + replacement)]

        elif isinstance(expr, murphi.VarExpr):
            if expr.typ.name in enum_value_map:
                self.enum_vars[str(expr) + replacement] = expr.typ.name
                if replacement == "":
                    return [Const(str(expr) + replacement, enum_value_map[expr.typ.name][expr.typ.name]), expr]
                else:
                    return [Const(str(expr) + replacement, enum_value_map[expr.typ.name][expr.typ.name])]
            else:
                if replacement == "":
                    return [z3.String(str(expr) + replacement), expr]
                else:
                    return [z3.String(str(expr) + replacement)]


        else:
            if replacement == "":

                return [z3.String(str(expr) + replacement), expr]
            else:
                return [z3.String(str(expr) + replacement)]

    def getVars(self, fomula, vardict, statements, replacement=""):
        # for guard and inv
        # print("fomula:",fomula)
        if isinstance(fomula, murphi.OpExpr):
            if self.isdigit(fomula):
                pass
            else:
                if isinstance(fomula.expr1, murphi.OpExpr) or isinstance(fomula.expr1, murphi.NegExpr) or isinstance(
                        fomula.expr2, murphi.OpExpr) or isinstance(fomula.expr2, murphi.NegExpr):
                    newlist1 = []
                    newlist2 = []
                    if isinstance(fomula.expr1, murphi.OpExpr) or isinstance(fomula.expr1, murphi.NegExpr):
                        _, newlist1 = self.getVars(fomula.expr1, vardict, newlist1, replacement)
                    if isinstance(fomula.expr2, murphi.OpExpr) or isinstance(fomula.expr2, murphi.NegExpr):
                        _, newlist2 = self.getVars(fomula.expr2, vardict, newlist2, replacement)
                    if len(newlist1) and len(newlist2):

                        statements.append(self.smtOP(newlist1[0], newlist2[0], fomula.op))
                    elif len(newlist2):
                        statements.append(newlist2[0])
                    elif len(newlist1):
                        statements.append(newlist1[0])
                else:
                    if isinstance(fomula.expr2, murphi.EnumValExpr) or isinstance(fomula.expr2, murphi.BooleanExpr) or (
                            isinstance(fomula.expr2, murphi.VarExpr) and fomula.expr2.name.isdigit()):
                        if str(fomula.expr1) + replacement not in vardict.keys():
                            vardict[str(fomula.expr1) + replacement] = self.setKey(fomula.expr1, replacement,
                                                                                   isbool=fomula.expr1 in self.boolVars,
                                                                                   isdigit=fomula.expr1 in self.scalarsetVars)
                        # self.pmurphi[str(fomula.expr2)] = fomula.expr2
                        val = self.getVal(fomula.expr2)
                        self.pmurphi[str(val)] = fomula.expr2
                        statements.append(self.smtOP(vardict[str(fomula.expr1) + replacement][0], val, fomula.op))
                    else:
                        if str(fomula.expr1) + replacement not in vardict.keys():
                            vardict[str(fomula.expr1) + replacement] = self.setKey(fomula.expr1, replacement,
                                                                                   isbool=fomula.expr1 in self.boolVars,
                                                                                   isdigit=fomula.expr1 in self.scalarsetVars)
                        # self.pmurphi[str(fomula.expr)] = fomula.expr
                        if str(fomula.expr2) + replacement not in vardict.keys():
                            vardict[str(fomula.expr2) + replacement] = self.setKey(fomula.expr2, replacement,
                                                                                   isbool=fomula.expr2 in self.boolVars,
                                                                                   isdigit=fomula.expr2 in self.scalarsetVars)
                        # self.pmurphi[vardict[str(fomula.expr2) + replacement][0]] = fomula.expr2
                        statements.append(self.smtOP(vardict[str(fomula.expr1) + replacement][0],
                                                     vardict[str(fomula.expr2) + replacement][0], fomula.op))

        # for assignment
        if isinstance(fomula, murphi.AssignCmd):
            if isinstance(fomula.expr, murphi.EnumValExpr) or isinstance(fomula.expr, murphi.BooleanExpr) or (
                    isinstance(fomula.expr, murphi.VarExpr) and fomula.expr.name.isdigit()):

                if str(fomula.var) + replacement not in vardict.keys():
                    vardict[str(fomula.var) + replacement] = self.setKey(fomula.var, replacement,
                                                                         isbool=fomula.var in self.boolVars,
                                                                         isdigit=fomula.var in self.scalarsetVars)

                # self.pmurphi[str(fomula.expr)] = fomula.expr
                val = self.getVal(fomula.expr)
                print("val:", val, type(val))
                self.pmurphi[str(val)] = fomula.expr
                statements.append(self.smtOP(vardict[str(fomula.var) + replacement][0], val, '='))
            else:
                expr_replacement = ""
                if str(fomula.var) + replacement not in vardict.keys():
                    vardict[str(fomula.var) + replacement] = self.setKey(fomula.var, replacement,
                                                                         isbool=fomula.var in self.boolVars,
                                                                         isdigit=fomula.var in self.scalarsetVars)
                # self.pmurphi[str(fomula.expr)] = fomula.expr
                if str(fomula.expr) + expr_replacement not in vardict.keys():
                    vardict[str(fomula.expr) + expr_replacement] = self.setKey(fomula.expr, expr_replacement,
                                                                               isbool=fomula.expr in self.boolVars,
                                                                               isdigit=fomula.expr in self.scalarsetVars)
                # self.pmurphi[vardict[str(fomula.expr) + expr_replacement][0]] = fomula.expr
                statements.append(self.smtOP(vardict[str(fomula.var) + replacement][0],
                                             vardict[str(fomula.expr) + expr_replacement][0], '='))

        # for negInv
        if isinstance(fomula, murphi.NegExpr):
            # assert isinstance(fomula.expr, murphi.OpExpr)
            if isinstance(fomula.expr, murphi.NegExpr):
                self.getVars(fomula.expr.expr, vardict, statements, replacement)
            else:
                if fomula.expr.op == '->':
                    # to cnf
                    cnf = murphi.OpExpr('&', fomula.expr.expr1, murphi.NegExpr(fomula.expr.expr2))
                    self.getVars(cnf, vardict, statements, replacement)
                if fomula.expr.op == '=':
                    neq = murphi.OpExpr('!=', fomula.expr.expr1, fomula.expr.expr2)
                    # print("neg:",neq,fomula.expr.expr2,type(fomula.expr.expr2))
                    self.getVars(neq, vardict, statements, replacement)
                if fomula.expr.op == '!=':
                    # print("!=:",murphi.OpExpr('=', fomula.expr.expr1, fomula.expr.expr2))
                    self.getVars(murphi.OpExpr('=', fomula.expr.expr1, fomula.expr.expr2), vardict, statements,
                                 replacement)
                if fomula.expr.op == '&':
                    # dnf = murphi.OpExpr('|', murphi.NegExpr(fomula.expr.expr1), murphi.NegExpr(fomula.expr.expr2))
                    # print("dnf:",dnf)
                    # self.getVars(dnf, vardict, statements, replacement)
                    impl = murphi.OpExpr('->', fomula.expr.expr1, murphi.NegExpr(fomula.expr.expr2))
                    self.getVars(impl, vardict, statements, replacement)
                if fomula.expr.op == '|':
                    cnf = murphi.OpExpr('&', murphi.NegExpr(fomula.expr.expr1), murphi.NegExpr(fomula.expr.expr2))
                    # print("cnf:",cnf)
                    self.getVars(cnf, vardict, statements, replacement)

        return vardict, statements


    def join_statements(self,statement):
        if len(statement) == 1:
            return statement[0]
        else:
            # return (str(statement[-1]) + "& (" + self.join_statements(statement[:-1]) + ")")
            return murphi.OpExpr('&',statement[-1],self.join_statements(statement[:-1]))

    def smtFormula(self):
        self.defEnum()

        # add enum values
        for enum_name, enum_typ in self.enum_typ_map.items():
            for enum_typ_name in enum_typ.names:
                if enum_typ_name not in self.pmurphi.keys():
                    self.pmurphi[enum_typ_name] = murphi.EnumValExpr(enum_typ, enum_typ_name)

        # for guard's variables
        self.variables, self.boundStates = self.getVars(self.guard,self.variables,self.boundStates)
        # # print("1. self.variables:",self.variables)
        # print("1. self.boundStates:",self.boundStates)
        # # print("1. self.pmurphi:", self.pmurphi)
        #
        for assign in self.assign:
            self.variables, self.boundStates  = self.getVars(assign, self.variables,self.boundStates,"'")
        #
        # # print("2. self.variables:",self.variables)
        # print("2. self.boundStates:",self.boundStates)
        # # print("2. self.pmurphi:", self.pmurphi)
        #
        # for assumption's variables
        for assumption in self.assumption:
            if str(assumption) not in self.variables.keys():
                self.variables[str(assumption)] = self.setKey(assumption, replacement="",
                                                              isbool=assumption in self.boolVars,
                                                              isdigit=assumption in self.scalarsetVars)
                print("assumption:")
                print(assumption)
                print(self.variables[str(assumption)][0],type(self.variables[str(assumption)][0]))                
                # if self.variables[str(assumption)][0] not in self.enum_EqulVars:
                    # self.enum_EqulVars.append(self.variables[str(assumption)][0])
            if str(assumption) + "'" not in self.variables.keys():
                self.variables[str(assumption) + "'"] = self.setKey(assumption, replacement="'",
                                                                    isbool=assumption in self.boolVars,
                                                                    isdigit=assumption in self.scalarsetVars)
            # self.boundStates.append(self.variables[str(assumption)][0] == self.variables[str(assumption)+"'"][0])
            self.boundStates.append(
                self.smtOP(self.variables[str(assumption)][0], self.variables[str(assumption) + "'"][0], '='))
        #
        # # print("3. self.variables:",self.variables)
        # print("3. self.boundStates:",self.boundStates)
        # # print("3. self.pmurphi:", self.pmurphi)
        #
        # for !inv's variables
        self.variables, self.boundStates = self.getVars(self.negInv, self.variables, self.boundStates, "'")
        # print("4. self.variables:",self.variables)
        # print("4. self.boundStates:", self.boundStates)
        # print("4. self.pmurphi:", self.pmurphi)

        # self.variables, self.boundStates = self.getVars(self.inv, self.variables,self.boundStates)
        # print("5. F:", self.boundStates)
        # print("5. self.pmurphi:", self.pmurphi)

        for ori_inv in self.ori_inv:
            # print("ori_inv:", ori_inv)
            self.variables, self.boundStates = self.getVars(ori_inv, self.variables, self.boundStates)

        dtype = None
        for data in self.data_permutations:
            if str(data) in self.pmurphi.keys():
                dtype = self.pmurphi[str(data)].typ
                break
        for data in self.data_permutations:
            if str(data) not in self.pmurphi.keys():
                self.pmurphi[str(data)] = murphi.VarExpr(str(data), dtype)

        for dvar in self.dataVars:
            print("data:", dvar)
            equalStates = []
            for data in self.data_permutations:
                val = self.getVal(data)
                equalStates.append(self.smtOP(self.variables[str(dvar)][0], val, '='))
            print("equalStates:", equalStates)
            if len(equalStates) == 1:
                self.boundStates.extend(equalStates)
            # elif len(equalStates)==2:
            #     self.boundStates.append(self.smtOP(equalStates[0], equalStates[1], '|'))
            elif len(equalStates) > 1:
                state1ptr = 0
                state2ptr = 1
                while state1ptr < len(equalStates):
                    if state2ptr < len(equalStates):
                        self.boundStates.append(self.smtOP(equalStates[state1ptr], equalStates[state2ptr], '|'))
                    state1ptr = state1ptr + 2
                    state2ptr = state2ptr + 2

        # print("6. self.variables:",self.variables)
        # print("6. self.pmurphi:", self.pmurphi)
        print("6. F:", self.boundStates)

        cti = {k: v for k, v in self.variables.items() if not k.endswith("'")}
        # print("cti:",cti)
        for state in self.boundStates:
            self.solver.add(state)
        print(self.solver.check())
        global callSmt
        callSmt = callSmt+1

        all_solutions = []
        inv_list = list()

        checksat = self.solver.check() == sat

        print("(self.enum_notEqulVars):",self.enum_notEqulVars)
        print("(self.enum_EqulVars):",self.enum_EqulVars)
        print("self.enum_notEqulVars_map:", self.enum_notEqulVars_map)
        print("1111:", self.solver.assertions())
        checkVars = [x for x in self.enum_notEqulVars if x not in self.enum_EqulVars]
        print("checkVars:",checkVars)
        vars = None
        if checkVars:
            vars = checkVars.pop(0)
        print("vars:", vars)
        while checksat:
            inv_list = []
            model = self.solver.model()
            print("Solution from z3:\n")
            print(model)

            digitNum = 0
            digitVar = None
            for k,v in cti.items():
                value=""
                print("model val type:",k,v,model[v[0]],type(model[v[0]]))
                # if isinstance(model[v[0]],SeqRef):
                if isinstance(model[v[0]],BoolRef):
                    value = str(is_true(model[v[0]]))
                elif isinstance(model[v[0]], DatatypeRef) or isinstance(model[v[0]], IntNumRef):
                    value = str(model[v[0]])
                    if isinstance(model[v[0]], IntNumRef):
                        digitNum +=1
                        digitVar = murphi.OpExpr('=', v[1], self.pmurphi[value])
                elif model[v[0]]==None:
                    pass
                else:
                    value = model[v[0]].as_string()

                # print("murphi表示:",murphi.OpExpr('=',v[1],self.pmurphi[value]))
                if value != "":

                    pattern = r'\S*\[.*?\]\S*'
                    # for var, m_var in cti.items():
                    if bool(re.search(pattern, k)):
                        if isinstance(v[1], murphi.ArrayIndex):
                            if {str(v[1]): str(v[1].idx.typ)} not in self.paraVars:
                                self.paraVars.append({str(v[1]): str(v[1].idx.typ)})
                        if isinstance(v[1], murphi.FieldName):
                            if {str(v[1]): str(v[1].v.idx.typ)} not in self.paraVars:
                                self.paraVars.append({str(v[1]): str(v[1].v.idx.typ)})

                    if value == "False":
                        inv_list.append(murphi.OpExpr('=', v[1], murphi.BooleanExpr(False)))
                    elif value == "True":
                        inv_list.append(murphi.OpExpr('=', v[1], murphi.BooleanExpr(True)))
                    elif value in self.pmurphi.keys():
                        # print("self.pmurphi:",self.pmurphi)
                        inv_list.append(murphi.OpExpr('=', v[1], self.pmurphi[value]))
                # inv_list.append(f"{v[0]} == {model[v[0]]}")
            print("invlist1:", inv_list)
            if digitNum == 1:
                inv_list.remove(digitVar)
                print("invlist2:", inv_list)
            print("paraVars:", self.paraVars)
            all_solutions.append(inv_list)
            print("inv already exist:",self.ori_inv)


            # checkVars = self.enum_notEqulVars - self.enum_EqulVars
            
            if vars!=None:
                addAssert = False
                # for vars in checkVars:
                print("vars:", vars)
                # print(model[cti[str(vars)][0]], type(model[cti[str(vars)][0]]))
                # if str(vars) in cti.keys() and model[cti[str(vars)][0]] != None and str(model[cti[str(vars)][0]]) not in self.enum_notEqulVars_map[str(vars)]:
                if str(vars) in cti.keys() and str(model[cti[str(vars)][0]]) in self.pmurphi.keys():
                    print("model[cti[str(vars)][0]]:", model[cti[str(vars)][0]], type(model[cti[str(vars)][0]]))
                    addAssert = True
                    print("add:")
                    print(cti[str(vars)][0] != model[cti[str(vars)][0]])
                    self.solver.add(cti[str(vars)][0] != model[cti[str(vars)][0]])
                    print("2222:", self.solver.assertions())
                elif str(vars) in cti.keys() and (model[cti[str(vars)][0]]==None or model[cti[str(vars)][0]]==""):
                    pass
                elif str(vars) in cti.keys() and model[cti[str(vars)][0]] not in self.pmurphi:
                    raise KeyError(f"the enum-type var {str(vars).upper()}'s value from SMT:{model[cti[str(vars)][0]]} not in pmurphi dict.")
                if addAssert:
                    print("add constrains")
                    checksat = self.solver.check() == sat
                    if checksat == False and checkVars:
                        print("check add unsat")
                        vars = checkVars.pop(0)
                    elif checksat == True:
                        print("check add sat.")
                    else:
                        vars = None
                else:
                    print("donot add constrains.")
                    checksat = False

            else:
                checksat = False

        aux_inv_list = list()
        if len(all_solutions)>0:
            for solution in all_solutions:
                print("solution:",solution)

                pattern = r'\[([^]]+)\]'
                invPattern_list = []
                for expr in solution:
                    invPattern_list.append(re.sub(pattern, r'[_]', str(expr)))
                if tuple(set(invPattern_list)) not in invlist_dict.keys():
                    invlist_dict[tuple(set(invPattern_list))] = None

                    self.call_LS(solution)
                    print("self.aux_inv1:",self.aux_inv)

                    if self.dataVars:
                        genericList, ScalarVarsDict = self.rematchScalarVars(self.aux_inv, [], {})             
                        if len(ScalarVarsDict) == 1:
                            self.aux_inv = None
                        elif ScalarVarsDict:
                            genericList.extend(self.linkage4ScalarVars(ScalarVarsDict))
                            self.aux_inv = murphi.NegExpr(self.join_statements(genericList))

                    print("self.aux_inv2:", self.aux_inv)
                    print("invPattern:",invPattern)
                    print("invPattern_dict:",invPattern_dict)


                    # deadlock暂时不需对称规约
                    newInvPattern = True
                    # newInvPattern = False
                    # if self.aux_inv != None:
                        # newInvPattern = self.symmetry_statute(self.aux_inv)
                    if newInvPattern and self.aux_inv != None:
                        print("add pattern:",self.aux_inv)
                        aux_inv_list.append(self.aux_inv)
                        self.murphiInvLines = self.murphi_paraInv(self.aux_inv)
                        with open(self.inv_path+"_invs.txt","a") as file:
                            file.write(f"invariant \"{self.name}\"\n")
                            file.write(murphi.indent(str(self.aux_inv),2))
                            file.write("\n")

                        # with open(self.inv_path+"_withInductiveInvs.m", "a") as file:
                        #     file.write("\n")
                        #     file.write(f"invariant \"{self.name}\"\n")
                        #     file.write(f"{self.murphiInvLines};\n")

                    else:
                        print("exist self.aux_inv:",self.aux_inv)
                        self.aux_inv = None



        return aux_inv_list,self.name


    def rematchScalarVars(self, OpExpr, invlist, ScalarVarsDict):
        if isinstance(OpExpr, murphi.NegExpr):
            self.rematchScalarVars(OpExpr.expr, invlist, ScalarVarsDict)
        elif isinstance(OpExpr, murphi.OpExpr):
            if OpExpr.op == '&' or OpExpr.op == '|' or OpExpr.op == '->':
                self.rematchScalarVars(OpExpr.expr1, invlist, ScalarVarsDict)
                self.rematchScalarVars(OpExpr.expr2, invlist, ScalarVarsDict)
            else:
                if str(OpExpr.expr2).isdigit():
                    if str(OpExpr.expr2) not in ScalarVarsDict.keys():
                        ScalarVarsDict[str(OpExpr.expr2)] = [OpExpr.expr1]
                    else:
                        ScalarVarsDict[str(OpExpr.expr2)].append(OpExpr.expr1)
                else:
                    invlist.append(OpExpr)

        return invlist, ScalarVarsDict

    def linkage4ScalarVars(self, ScalarVarsDict):
        ScalarVarsLinkage = []
        Neglist = []
        def constructEqual(Varlist):
            if len(Varlist)==1:
                return Varlist[0]
            return murphi.OpExpr('=',Varlist[-1],constructEqual(Varlist[:-1]))
        def constructNegEqual(Varlist):
            if len(Varlist)==1:
                return Varlist[0]
            return murphi.OpExpr('!=',Varlist[-1],constructNegEqual(Varlist[:-1]))
        for num, vars in ScalarVarsDict.items():
            Neglist.append(vars[0])
            if len(vars)>1:
                ScalarVarsLinkage.append(constructEqual(vars))
        ScalarVarsLinkage.append(constructNegEqual(Neglist))
        return ScalarVarsLinkage



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

    # 对称规约
    def count_values(self, var_list):
        value_counts = {}
        pattern = r'\[(\d+)\]'
        nodeVals = []
        for dictionary in var_list:
            for varName, value in dictionary.items():
                if re.findall(pattern, varName) in nodeVals:
                    pass
                else:
                    nodeVals.append(re.findall(pattern, varName))
                    if value in value_counts:
                        value_counts[value] += 1
                    else:
                        value_counts[value] = 1
        return value_counts

    def parse_statements(self,statement,subcon):
        if isinstance(statement, murphi.NegExpr):
            self.parse_statements(statement.expr,subcon)
        elif isinstance(statement, murphi.OpExpr) and statement.op=='&':
            if isinstance(statement.expr1, murphi.OpExpr) and statement.expr1.op=='&':
                self.parse_statements(statement.expr1, subcon)
            else:
                subcon.append(statement.expr1)
            if isinstance(statement.expr2, murphi.OpExpr) and statement.expr2.op=='&':
                self.parse_statements(statement.expr2, subcon)
            else:
                subcon.append(statement.expr2)
        return subcon

    def OpExprEq(self,OpExpr,patternlist,pattern):
        Oplist = []
        var_pattern = r'\S*\[.*?\]\S*'
        self.var_list = []
        vardict = dict()
        matches = []
        for item in OpExpr:
            Oplist.append(re.sub(pattern, r'[_]', str(item)))
            matches.extend(re.findall(var_pattern, str(item)))
        matches = set(matches)
        print("matches:",matches)
        for var in self.paraVars:
            print("var.keys():",list(var.keys())[0])
            if list(var.keys())[0] in set(matches):
                self.var_list.append(var)
        print("var_list:",self.var_list)
        vardict = self.count_values(self.var_list)
            #         varlist.append(var)
        print("Oplist:",Oplist)
        print("set(Oplist):", set(Oplist))
        print("vardict:", vardict)
        for pattern in patternlist:
            print("pattern:", pattern)
            print("set(pattern):", set(pattern))
            print(invPattern_dict[tuple(pattern)])
            if set(pattern) == set(Oplist) and invPattern_dict[tuple(pattern)] == vardict:
                return True
        invPattern.append(Oplist)
        invPattern_dict[tuple(Oplist)] = vardict
        return False


    def symmetry_statute(self,inv):
        pattern = r'\[([^]]+)\]'
        inv_cons = self.parse_statements(inv,[])
        if self.OpExprEq(inv_cons,invPattern,pattern):
            return False
        return True



        # pattern = r'\[([^]]+)\]'
        # # print("saveInvPattern:",str(inv))
        # abInv = re.sub(pattern, r'[_]', str(inv))
        # for invpattern in invPattern:
        #     con2 = self.parse_statements(invpattern,[])
        #     print("con2:",con2)
        #     print("abInv:",abInv)
        #     print("invpattern:",invpattern)
        #     if set(invpattern) == set(abInv):
        #         print("set(abInv):",set(abInv))
        #         return False
        # invPattern.append(abInv)
        # return True



    def call_cmurphi(self, inv_list):
        global callLS
        callLS = callLS+1
        can_inv = murphi.NegExpr(self.join_statements(inv_list))
        # print(f"invariant '{self.name}'\n {murphi.indent(str(can_inv),2)};")
        new_inv = f"invariant \"{self.name}\"\n {murphi.indent(str(can_inv),2)};"
        print("new_inv:",new_inv)
        self.appendInv_and_save(self.inv_path+"_withoutInv.m", new_inv, self.inv_path+"_newTmp.m")

        cmurphi_path = '../cmurphi_LS'
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

        lsOutput = stdoutdata.decode('utf-8')
        pattern_counter = re.compile(r'Invariant\s"(\w+).*"\sfailed')
        counter_ex = re.findall(pattern_counter, lsOutput)

        pattern_pass = "No error found."

        pattern_undefined = re.compile(r'The undefined value at (\w+).* is referenced')
        undefined_ex = re.findall(pattern_undefined, lsOutput)

        os.remove('%s_newTmp.cpp' % file)
        os.remove('%s_newTmp.o' % file)
        # os.remove('%s_newTmp.m' % file)

        if undefined_ex:
            raise ValueError(f"var {undefined_ex} is undefined at candidate invariant:\n{new_inv}\n!")


        if not counter_ex and pattern_pass in lsOutput:
            print('No cti found. The invariants are OK.')
            return False,can_inv
        elif not counter_ex and pattern_pass not in lsOutput:
            raise ValueError(f"error when LS check the following candidate invariant:\n{new_inv}\n")
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

    def dedoubleNeg(self,fomula):
        if isinstance(fomula, murphi.NegExpr) and isinstance(fomula.expr, murphi.NegExpr):
            return fomula.expr.expr
        else:
            return fomula

    def get_inv_var_length(self,inv,inv_var_length):
        assert isinstance(inv, murphi.OpExpr)
        if isinstance(inv.expr1, murphi.OpExpr):
            inv_var_length = self.get_inv_var_length(inv.expr1,inv_var_length)
        if isinstance(inv.expr2, murphi.OpExpr):
            inv_var_length = self.get_inv_var_length(inv.expr2,inv_var_length)
        if isinstance(inv.expr1, murphi.ArrayIndex):
            return inv_var_length+1
        if isinstance(inv.expr2, murphi.ArrayIndex):
            return inv_var_length+1
        return inv_var_length

        # if isinstance(inv.expr2, murphi.OpExpr):
        #     self.get_inv_var_map(inv.expr2)

    def get_inv_var_map(self,inv,inv_list):
        assert isinstance(inv, murphi.OpExpr)
        if isinstance(inv.expr1, murphi.OpExpr):
            self.get_inv_var_map(inv.expr1, inv_list)
        elif isinstance(inv.expr1, murphi.EnumValExpr) or isinstance(inv.expr1, murphi.BooleanExpr):
            pass
        else:
            if inv.expr1 not in inv_list:
                inv_list.append(inv.expr1)
        if isinstance(inv.expr2, murphi.OpExpr):
            self.get_inv_var_map(inv.expr2, inv_list)
        elif isinstance(inv.expr2, murphi.EnumValExpr) or isinstance(inv.expr2, murphi.BooleanExpr):
            pass
        else:
            if inv.expr2 not in inv_list:
                inv_list.append(inv.expr2)

        return inv_list

    def murphi_paraInv(self,inv):
        inv = str(inv)
        inv_str = ""
        subdict = {}
        for para in self.var_list:
            for var,typ in para.items():
                pattern = r'\[(\d+)\]'
                para_num = re.findall(pattern, var)[0]
                inv_str = inv_str + murphi.indent(f"forall {chr(ord('i')+int(para_num)-1)} : {typ} do\n", 2)
                subdict[var] = var.replace(para_num,chr(ord('i')+int(para_num)-1))

        for arg_var, para_var in subdict.items():
            inv =  murphi.indent(inv.replace(arg_var, para_var), 2)
        inv_str = inv_str + inv + "\n"

        for idx in range(len(self.var_list)):
            inv_str = inv_str + "end" + murphi.indent("", 2)
        inv_str = inv_str + ";"
        print("inv_str:\n", inv_str)
        return inv_str


def search4new_auxInv(inv_name,new_inv):
    print("new_inv:",new_inv)
    c.inv_instance = {}
    c.inv_var_length = {}
    c.rule_var_ins = {}
    c.ins_var_dict = {}
    c.formula_instances = {}

    c.inv_instance = {inv_name:new_inv}
    new_inv = constructF.dedoubleNeg(new_inv)
    inv_var_length = constructF.get_inv_var_length(new_inv.expr, 0)
    c.inv_var_length[inv_name] = inv_var_length

    inv_var_map = {}
    inv_var_list = []
    inv_var_map[inv_name] = constructF.get_inv_var_map(new_inv.expr,inv_var_list)
    c.ins_var_dict = inv_var_map

    c.getBooleanVars(new_inv)
    c.getRules()

def trans2IVY(parse_path, ivyselect):
    prot = parse_file(parse_path + ".m", ivyselect)
    if ivyselect:
        save = parse_path + ".ivy"
    else:
        save = parse_path + "_out.m"
    with open(save, "w") as f:
        f.write(str(prot))

def run_ivy(ivyFilePath):
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

if __name__ == "__main__":

    start_time = time.time()

    # parse_name = "../protocols/mutualEx/mutualEx"
    parse_name = "protocols/mutdata/mutdata"
    # parse_name = "protocols/german/german"
    # parse_name = "protocols/german_withoutData/german_withoutData"
    # inv_path = parse_name
    inv_path = sys.argv[1]
    node_permutations = [int(x) for x in sys.argv[2:]]
    # shutil.copyfile(inv_path + ".m", inv_path + "_withInductiveInvs.m")
    # inv_file = open(inv_path, "w")
    # GetSMTformula(parse_name=parse_name).getRules()
    c = constructSMT.GetSMTformula(parse_name=inv_path, node_permutations=node_permutations)
    c.getInvs()
    ori_inv = defaultdict(list)
    print("c.inv_instance:",c.inv_instance)
    for key, value in c.inv_instance.items():
        ori_inv[key.split("_")[0]].append(value)
    print("ori_inv:",ori_inv)
    # print(c.formula_instances)

    # old instance的值deepcope一份

    i=5
    auxInv_dict = dict()
    while(True):
        for name,instance in c.formula_instances.items():
            # print("i是:",i)
            print(name,instance)
            current_inv = name.split("_")[0]
            print("current_inv:", current_inv)
            constructF = ConstructF(name, instance, inv_path, ori_inv[current_inv], c.booleanExpr_list, c.enum_typ_map, c.typ_map, c.scalarsetVars, c.data_permutations)
            new_inv_list, inv_name = constructF.smtFormula()

            if len(new_inv_list)>0:
                ori_inv[current_inv].extend(new_inv_list)
                for i,new_inv in enumerate(new_inv_list):
                    auxInv_dict[inv_name+'_'+str(i+1)] = new_inv
        if len(auxInv_dict)!=0:
            first_key = next(iter(auxInv_dict))
            print("list0:", auxInv_dict)
            search4new_auxInv(first_key,auxInv_dict[first_key])
            auxInv_dict.pop(first_key)
            print("list1:",auxInv_dict)
        else:
            print("times of calling SMT:",callSmt)
            print("times of calling LocalSearch:", callLS)
            with open(inv_path+"EfficiencyAna.txt", 'w') as new_file:
                new_file.write(f"times of calling SMT:{callSmt}\n")
                new_file.write(f"times of calling LocalSearch:{callLS}\n")
            break

        i=i-1
        # 做完smt check之后，如果发现inv_instance为空了，那么说明已经没有更多反例，已找到归纳不变式
        # 如果inv_instance不为空，那么说明有反例，需要构造新的formula_instances

    # 转换到ivy格式并调用ivy check
    # ivyselect = "#lang ivy1.7"
    # trans2IVY(inv_path + "_withInductiveInvs", ivyselect)
    # run_ivy(inv_path + "_withInductiveInvs" + ".ivy")
    end_time = time.time()
    elapsed_time = end_time - start_time
    print(f"program runtime: {elapsed_time:.6f} s")

    
