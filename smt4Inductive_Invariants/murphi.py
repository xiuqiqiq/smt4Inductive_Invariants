import re
import random
import string

def indent(s, num_space, first_line=None):
    lines = s.split('\n')
    if first_line is None:
        return '\n'.join(' ' * num_space + line for line in lines)
    else:
        res = ' ' * first_line + lines[0]
        if len(lines) > 1:
            res += '\n' + '\n'.join(' ' * num_space + line for line in lines[1:])
        return res

ivySelect = ""
record_map = dict()
record_vars_map = dict()
def check_ivy(string):
    match = re.search(r"ivy", string)
    if match:
        return True
    else:
        return False

def generate_random_letters(upper_or_lower):
    # letters = list(string.ascii_uppercase)
    # random_letters = random.sample(letters, n)
    if upper_or_lower == "upper":
        return random.choice(string.ascii_uppercase)
    if upper_or_lower == "lower":
        return random.choice(string.ascii_lowercase)

class MurphiConstDecl:
    def __init__(self, name, val):
        assert isinstance(name, str)
        self.name = name
        self.val = val

    def __str__(self):
        return "%s : %s" % (self.name, self.val)

    def __repr__(self):
        return "MurphiConst(%s, %s)" % (self.name, self.val)

    def __eq__(self, other):
        return isinstance(other, MurphiConstDecl) and self.name == other.name and self.val == other.val

class RngConst:
    pass

class IntRngConst(RngConst):
    def __init__(self, val):
        #assert isinstance(name, str)
        self.val = val

    def __str__(self):
        return "%d" % ( self.val)

    def __repr__(self):
        return "IntRngConst(%d)" %  self.val

    def __eq__(self, other):
        return isinstance(other, IntRngConst) and self.val == other.val

class NameRngConst(RngConst):
    def __init__(self, name):
        assert isinstance(name, str)
        self.val = name

    def __str__(self):
        return "%s" % ( self.name)

    def __repr__(self):
        return "IntRngConst(%s)" %  self.name

    def __eq__(self, other):
        return isinstance(other, NameRngConst) and self.name == other.name

class MurphiType:
    pass

class VarType(MurphiType):
    def __init__(self, name):
        if check_ivy(ivySelect):
            self.name = name.lower()+"_t"
        else:
            self.name = name

    def __str__(self):
        return self.name

    def __repr__(self):
        return "VarType(%s)" % self.name

    def __eq__(self, other):
        return isinstance(other, VarType) and self.name == other.name

class RngType(MurphiType):
    def __init__(self, downRng:str,upRng:str):
        assert isinstance(downRng, str)
        assert isinstance(upRng, str)

        self.downRng = downRng
        self.upRng =upRng

    def __str__(self):
        print(self.downRng)
        print(self.upRng)
        #return(self.downRng+".."+self.upRng)
        return "%s..%s" % (self.downRng, self.upRng)

    def __repr__(self):
        return "RangeType (is %s .. %s)" % ( self.downRng, self.upRng)

    def __eq__(self, other):
        return isinstance(other, RngType) and self.downRng == other.downRng and self.upRng==other.upRng

class BooleanType(MurphiType):
    def __init__(self):
        pass

    def __str__(self):
        if check_ivy(ivySelect):
            return "bool"
        else:
            return "boolean"

    def __repr__(self):
        return "BooleanType()"

    def __eq__(self, other):
        return isinstance(other, BooleanType)

class ScalarSetType(MurphiType):
    def __init__(self, const_name: str):
        assert isinstance(const_name, str)
        self.const_name = const_name

    def __str__(self):
        return "scalarset(%s)" % self.const_name

    def __repr__(self):
        return "ScalarSetType(%s)" % self.const_name

    def __eq__(self, other):
        return isinstance(other, ScalarSetType) and self.const_name == other.const_name

class UnionType(MurphiType):
    def __init__(self, typs):
        self.typs = typs

    def __str__(self):
        if check_ivy(ivySelect):
            # res = "struct {\n"
            # for var_typ in self.typs:
            #     union_sub_type = random.choice(string.ascii_lowercase)
            #     res += indent(union_sub_type,2) + ":" + var_typ.name + ","
            return ""
            # return "struct {\n%s\n}" % (', '.join(str(typ) for typ in self.typs))
        else:
            return "union {%s}" % (', '.join(str(typ) for typ in self.typs))

    def __repr__(self):
        return "UnionType(%s)" % (', '.join(repr(typ) for typ in self.typs))

    def __eq__(self, other):
        return isinstance(other, UnionType) and self.typs == other.typs

class EnumType(MurphiType):
    def __init__(self, names):
        self.names = names

    def __str__(self):
        if check_ivy(ivySelect):
            return "{%s}" % (', '.join(name for name in self.names))
        else:
            return "enum {%s}" % (', '.join(name for name in self.names))

    def __repr__(self):
        return "EnumType(%s)" % (', '.join(repr(name) for name in self.names))

    def __eq__(self, other):
        return isinstance(other, EnumType) and self.names == other.names

class ArrayType(MurphiType):
    def __init__(self, idx_typ, ele_typ):
        self.idx_typ = idx_typ
        self.ele_typ = ele_typ

    def __str__(self):
        if check_ivy(ivySelect):
            return "(%s) : %s" % (random.choice(string.ascii_uppercase) + ":" + str(self.idx_typ), self.ele_typ)
        else:
            return "array [%s] of %s" % (self.idx_typ, self.ele_typ)
    def __repr__(self):
        return "ArrayType(%s, %s)" % (repr(self.idx_typ), repr(self.ele_typ))

    def __eq__(self, other):
        return isinstance(other, ArrayType) and self.idx_typ == other.idx_typ and \
            self.ele_typ == other.ele_typ

class RecordType(MurphiType):
    def __init__(self, typ_decls):
        self.typ_decls = typ_decls

    def __str__(self):
        return "record\n%s\nend" % ('\n'.join(indent(str(decl), 2) + ';' for decl in self.typ_decls))

    def __repr__(self):
        return "RecordType(%s)" % (', '.join(repr(decl) for decl in self.typ_decls))

    def __eq__(self, other):
        return isinstance(other, RecordType) and self.typ_decls == other.typ_decls

union_dict = dict()
class MurphiTypeDecl:
    def __init__(self, name, typ):
        self.name = name
        self.typ = typ

    def __str__(self):
        if check_ivy(ivySelect):
            if isinstance(self.typ,ScalarSetType):
                return "%s" % self.name
            elif isinstance(self.typ, UnionType):
                res = self.name + " = struct {\n"
                typ_list = list()
                for i in range(len(self.typ.typs)-1):
                    subtyp_name = self.name+"_"+self.typ.typs[i].name
                    typ_list.append([self.typ.typs[i].name,subtyp_name])
                    res += indent(subtyp_name,2) + ":" + self.typ.typs[i].name + "," + "\n"
                subtyp_name = self.name + "_" + self.typ.typs[len(self.typ.typs)-1].name
                typ_list.append([self.typ.typs[len(self.typ.typs)-1].name,subtyp_name])
                global union_dict
                union_dict[self.name] = typ_list
                res += indent(subtyp_name, 2) + ":" + self.typ.typs[len(self.typ.typs)-1].name + "\n" +"}"
                # print("union_dict:",union_dict)
                return res
            else:
                return "%s = %s" % (self.name, self.typ)
        else:
            return "%s : %s" % (self.name, self.typ)

    def __repr__(self):
        return "MurphiTypeDecl(%s, %s)" % (repr(self.name), repr(self.typ))

    def __eq__(self, other):
        return isinstance(other, MurphiTypeDecl) and self.name == other.name and \
            self.typ == other.typ

class MurphiVarDecl:
    def __init__(self, name, typ):
        self.name = name
        self.typ = typ

    def __str__(self):
        if check_ivy(ivySelect):

            global union_dict
            # print(str(self.typ))
            # if isinstance(self.typ,VarType) and self.typ.name in union_dict.keys():
            #     print(self.typ)
            self.name = self.name.lower()+"_v"
            if isinstance(self.typ, ArrayType):
                # for key in record_map.keys():
                #     # print(str(self.typ))
                #     if key in str(self.typ):
                #         print(key,self.name,str(self.typ))
                return "%s%s" % (self.name, self.typ)
            ## 6.11 如果当前的var，在record_map的key()中，重新命名变量
            # elif (key in str(self.typ) for key in record_map.keys()):
            #     print("self.name:",self.name,str(self.typ))
            #     return ""
            else:
                return "%s : %s" % (self.name, self.typ)
        else:
            return "%s : %s" % (self.name, self.typ)

    def __repr__(self):
        return "MurphiVarDecl(%s, %s)" % (repr(self.name), repr(self.typ))

    def __eq__(self, other):
        return isinstance(other, MurphiVarDecl) and self.name == other.name and \
            self.typ == other.typ

class BaseExpr:
    pass

class UnknownExpr(BaseExpr):
    def __init__(self, s):
        self.s = s

    def priority(self):
        return 100

    def __str__(self):
        return "#%s#" % self.s

    def __repr__(self):
        return "UnknownExpr(%s)" % repr(self.s)

    def elaborate(self, prot, bound_vars):
        assert isinstance(prot, MurphiProtocol)
        if self.s == "true":
            return BooleanExpr(True)
        elif self.s == "false":
            return BooleanExpr(False)
        elif self.s in prot.enum_map:
            return EnumValExpr(prot.enum_map[self.s], self.s)
        elif self.s in prot.ori_enum_map and self.s.lower()+"_em" in prot.enum_map:
            self.s = self.s.lower()+"_em"
            return EnumValExpr(prot.enum_map[self.s], self.s)
        elif self.s in bound_vars:
            return VarExpr(self.s, bound_vars[self.s])
        elif self.s in prot.var_map:
            return VarExpr(self.s, prot.var_map[self.s])
        elif self.s.lower()+"_v" in prot.var_map:
            self.s = self.s.lower() + "_v"
            return VarExpr(self.s, prot.var_map[self.s])
        else:
            return VarExpr(self.s, prot.var_map[self.s]) #revise raise AssertionError("elaborate: unrecognized name %s" % self.s)

class BooleanExpr(BaseExpr):
    def __init__(self, val):
        self.val = val

    def priority(self):
        return 100

    def __str__(self):
        if self.val:
            return "true"
        else:
            return "false"

    def __repr__(self):
        return "BooleanExpr(%s)" % repr(self.val)

    def __eq__(self, other):
        return isinstance(other, BooleanExpr) and self.val == other.val

    def elaborate(self, prot, bound_vars):
        return self

class EnumValExpr(BaseExpr):
    def __init__(self, enum_type, enum_val):
        self.enum_type = enum_type
        self.enum_val = enum_val


    def priority(self):
        return 100

    def __str__(self):
        return self.enum_val

    def __repr__(self):
        return "EnumValExpr(%s, %s)" % (repr(self.enum_type), repr(self.enum_val))

    def __eq__(self, other):
        return isinstance(other, EnumValExpr) and self.enum_type == other.enum_type and \
            self.enum_val == other.enum_val

    def elaborate(self, prot, bound_vars):
        return self

class VarExpr(BaseExpr):
    def __init__(self, name, typ):
        self.name = name
        self.typ = typ


    def priority(self):
        return 100

    def __str__(self):
        # global union_dict
        # if str(self.typ) in union_dict.keys():
        #     print(self.name,";",self.typ)
        return str(self.name)

    def __repr__(self):
        return "VarExpr(%s)" % repr(self.name)

    def __eq__(self, other):
        return isinstance(other, VarExpr) and self.name == other.name and self.typ == other.typ

    def elaborate(self, prot, bound_vars):
        return self

class FieldName(BaseExpr):
    def __init__(self, v, field):
        self.v = v
        self.field = field

    def priority(self):
        return 100

    def __str__(self):
        if check_ivy(ivySelect):
            if str(self.v).split("(")[0] in record_vars_map.keys():
                # print(str(self.v).split("(")[0],record_vars_map[str(self.v).split("(")[0]])
                if str(self.field) in record_vars_map[str(self.v).split("(")[0]].keys():
                    print(str(self.v)+"."+str(self.field)+"  to  "+record_vars_map[str(self.v).split("(")[0]][str(self.field)]+"("+str(self.v).split("(")[1])
                    return  record_vars_map[str(self.v).split("(")[0]][str(self.field)]+"("+str(self.v).split("(")[1]
        else:
            return "%s.%s" % (self.v, self.field)

    def __repr__(self):
        return "FieldName(%s, %s)" % (repr(self.v), repr(self.field))

    def __eq__(self, other):
        return isinstance(other, FieldName) and self.v == other.v and self.field == other.field

    def elaborate(self, prot, bound_vars):
        return FieldName(self.v.elaborate(prot, bound_vars), self.field)

class ArrayIndex(BaseExpr):
    def __init__(self, v, idx):
        self.v = v
        self.idx = idx

    def priority(self):
        return 100

    def __str__(self):
        if check_ivy(ivySelect):
            return "%s(%s)" % (self.v, self.idx)
        else:
            return "%s[%s]" % (self.v, self.idx)

    def __repr__(self):
        return "ArrayIndex(%s, %s)" % (repr(self.v), repr(self.idx))

    def __eq__(self, other):
        return isinstance(other, ArrayIndex) and self.v == other.v and self.idx == other.idx

    def elaborate(self, prot, bound_vars):
        return ArrayIndex(self.v.elaborate(prot, bound_vars), self.idx.elaborate(prot, bound_vars))

invVars = dict()
class ForallExpr(BaseExpr):
    def __init__(self, var_decl, expr):
        self.var_decl = var_decl
        self.var, self.typ = self.var_decl.name, self.var_decl.typ
        self.expr = expr

    def priority(self):
        return 70

    def __str__(self):
        if check_ivy(ivySelect):
            global invVars
            invVars.update({self.var:self.var.upper()})
            res = " " + str(self.expr) + "\n"
            if isinstance(self.expr, OpExpr):
                pattern = re.compile(r'\b(' + '|'.join(re.escape(key) for key in invVars.keys()) + r')\b')
                res = pattern.sub(lambda x: invVars[x.group()], res)
            return res
        else:
            res = "forall %s do\n" % self.var_decl
            res += indent(str(self.expr), 2) + "\n"
            res += "end"
            return res

    def __repr__(self):
        return "ForallExpr(%s, %s)" % (repr(self.var_decl), repr(self.expr))

    def __eq__(self, other):
        return isinstance(other, ForallExpr) and self.var_decl == other.var_decl and \
            self.expr == other.expr

    def elaborate(self, prot, bound_vars):
        bound_vars[self.var] = self.typ
        res = ForallExpr(self.var_decl, self.expr.elaborate(prot, bound_vars))
        del bound_vars[self.var]
        return res

priority_map = {
    '+': 60,
    '=': 50,
    '!=': 50,
    '&': 35,
    '|': 30,
    '->': 25
}

class OpExpr(BaseExpr):
    def __init__(self, op, expr1, expr2):
        assert isinstance(op, str) and op in ("+",'=', '!=', '&', '|', '->')
        assert isinstance(expr1, BaseExpr), "OpExpr: expr1 %s has type %s" % (expr1, type(expr1))
        assert isinstance(expr2, BaseExpr), "OpExpr: expr2 %s has type %s" % (expr2, type(expr2))
        self.op = op
        self.expr1 = expr1
        self.expr2 = expr2

    def priority(self):
        return priority_map[self.op]

    def __str__(self):
        s1, s2 = str(self.expr1), str(self.expr2)
        if self.expr1.priority() <= self.priority():
            if '\n' in s1:
                s1 = "(" + indent(s1, 2, first_line=1) + " )"
            else:
                s1 = "(" + s1 + ")"
        if self.expr2.priority() < self.priority():
            if '\n' in s2:
                s2 = "(" + indent(s2, 2, first_line=1) + " )"
            else:
                s2 = "(" + s2 + ")"
        if self.op in ("="):
            return "%s %s %s" % (s1, self.op, s2)
        if self.op in ("!="):
            if check_ivy(ivySelect):
                return "%s ~= %s" % (s1, s2)
            else:
                return "%s %s %s" % (s1, self.op, s2)
        elif self.op in ('&', '|'):
            return "%s %s %s" % (s1, self.op, s2)
        elif self.op in ('->'):
            if isinstance(self.expr2, OpExpr) and self.expr2.op == '->':
                return "%s -> (%s)" % (s1, indent(s2, 2))
            else:
                return "%s -> %s" % (s1, indent(s2, 2))
        else:
            raise NotImplementedError

    def getVars(self):
        print(self.expr1,self.expr2)

    def __repr__(self):
        return "OpExpr(%s, %s, %s)" % (self.op, self.expr1, self.expr2)

    def __eq__(self, other):
        return isinstance(other, OpExpr) and self.op == other.op and self.expr1 == other.expr1 and \
            self.expr2 == other.expr2

    def elaborate(self, prot, bound_vars):
        return OpExpr(self.op, self.expr1.elaborate(prot, bound_vars), self.expr2.elaborate(prot, bound_vars))

class NegExpr(BaseExpr):
    def __init__(self, expr):
        self.expr = expr

    def priority(self):
        return 80

    def __str__(self):
        s = str(self.expr)
        if self.expr.priority() < self.priority():
            s = "(" + s + ")"
        return "!" + s

    def __repr__(self):
        return "NegExpr(%s)" % self.expr

    def __eq__(self, other):
        return isinstance(other, NegExpr) and self.expr == other.expr

    def elaborate(self, prot, bound_vars):
        return NegExpr(self.expr.elaborate(prot, bound_vars))

class BaseCmd:
    pass

class Skip(BaseCmd):
    def __init__(self):
        pass

    def __str__(self):
        return "skip;"

    def __repr__(self):
        return "Skip()"

    def __eq__(self, other):
        return isinstance(other, Skip)

    def elaborate(self, prot, bound_vars):
        return self

class UndefineCmd(BaseCmd):
    def __init__(self, var):
        self.var = var

    def __str__(self):
        if check_ivy(ivySelect):
            return ""
        else:
            return "undefine %s;" % self.var

    def __repr__(self):
        return "UndefineCmd(%s)" % repr(self.var)

    def __eq__(self, other):
        return isinstance(other, UndefineCmd) and self.var == other.var

    def elaborate(self, prot, bound_vars):
        return UndefineCmd(self.var.elaborate(prot, bound_vars))

datas = dict()
equal_datas = dict()
class AssignCmd(BaseCmd):
    def __init__(self, var, expr):
        assert isinstance(var, BaseExpr)
        # print(record_map)
        self.var = var
        self.expr = expr

    def __str__(self):
        if check_ivy(ivySelect):
            if isinstance(self.var, VarExpr) and isinstance(self.expr, VarExpr) and re.search("data",
                                                                                              self.expr.typ.name):
                # print(datas)
                return ""
            else:
                return indent("%s := %s;\n" % (self.var, self.expr), 2)
        else:
            return indent("%s := %s;\n" % (self.var, self.expr), 2)

    def __repr__(self):
        return "AssignCmd(%s, %s)" % (repr(self.var), repr(self.expr))

    def __eq__(self, other):
        return isinstance(other, AssignCmd) and self.var == other.var and self.expr == other.expr

    def elaborate(self, prot, bound_vars):
        return AssignCmd(self.var.elaborate(prot, bound_vars), self.expr.elaborate(prot, bound_vars))

def paraDataVars(value,equal_vars):
    cmds = set()
    equal_vars = set(equal_vars)
    for i in range(len(equal_vars)-1,0,-1):
        cmds.add(f"{list(equal_vars)[i]} := {list(equal_vars)[i-1]}")
    return cmds


class ForallCmd(BaseCmd):
    def __init__(self, var_decl, cmds):
        self.var_decl = var_decl
        self.var, self.typ = self.var_decl.name, self.var_decl.typ
        self.cmds = cmds


    def __str__(self):
        if check_ivy(ivySelect):
            res=''
            for cmd in self.cmds:
                if isinstance(cmd.var,VarExpr) and re.search("data", cmd.expr.typ.name):
                    datas[cmd.var.name] = cmd.expr.name
                res += str(cmd)
                # pattern = r"\[(.*?)\]"
                # match = re.search(pattern, res)
                # if match:
                #     found_string = match.group(1)
                #     if found_string == self.var:
                #         replacement = "(" + found_string.upper() + ")"
                #         res = re.sub(re.escape(match.group(0)), replacement, res)

            cmds = set()
            for var,value in datas.items():
                if value in equal_datas:
                    equal_datas[value].append(var)
                else:
                    equal_datas[value] = [var]
            for value, vars in equal_datas.items():
                cmds = cmds | paraDataVars(value,vars)
            # for value,vars in equal_datas.items():
            #     for cmd in self.cmds:
            #         if isinstance(cmd.var, VarExpr) and cmd.var.name in vars:
            #             if len(vars)>1:
            #                 print(cmd)

                # if self.var in vars:
                #     print(self.var,",",value)
                # if len(vars) >1:
                #     print(f"值为 {value} 的键：{vars}")
            for cmd in cmds:
                res += indent(str(cmd), 2) + ";" + "\n"
            return res
        else:
            res = "for %s do\n" % self.var_decl
            for cmd in self.cmds:
                res += indent(str(cmd), 2) + "\n"
            res += "end;"
            return res

    def __repr__(self):
        return "ForallCmd(%s, %s)" % (repr(self.var_decl), repr(self.cmds))

    def __eq__(self, other):
        return isinstance(other, ForallCmd) and self.var_decl == other.var_decl and \
            self.cmds == other.cmds

    def elaborate(self, prot, bound_vars):
        bound_vars[self.var] = self.typ
        res = ForallCmd(self.var_decl, [cmd.elaborate(prot, bound_vars) for cmd in self.cmds])
        del bound_vars[self.var]
        return res

class IfCmd(BaseCmd):
    def __init__(self, args):
        assert len(args) >= 2, "IfCmd: input args has %s elements" % len(args)
        self.args = args

        self.if_branches = []
        self.else_branch = None
        for i in range(len(self.args) // 2):
            self.if_branches.append((self.args[2*i], self.args[2*i+1]))
        if len(self.args) % 2 == 1:
            self.else_branch = self.args[-1]

    def __str__(self):
        res = "if %s then\n" % self.if_branches[0][0]
        for cmd in self.if_branches[0][1]:
            res += indent(str(cmd), 2) + "\n"
        for i in range(1, len(self.if_branches)):
            res += "elsif %s then\n" % self.if_branches[i][0]
            for cmd in self.if_branches[i][1]:
                res += indent(str(cmd), 2) + "\n"
        if self.else_branch:
            res += "else\n"
            for cmd in self.else_branch:
                res += indent(str(cmd), 2) + "\n"
        res += "end;"
        return res

    def __repr__(self):
        return "IfCmd(%s)" % repr(self.args)

    def __eq__(self, other):
        return isinstance(other, IfCmd) and self.args == other.args

    def elaborate(self, prot, bound_vars):
        new_args = []
        for arg in self.args:
            if isinstance(arg, BaseExpr):
                new_args.append(arg.elaborate(prot, bound_vars))
            else:
                new_args.append([cmd.elaborate(prot, bound_vars) for cmd in arg])
        return IfCmd(new_args)

class StartState:
    def __init__(self, name, cmds):
        self.name = name
        self.cmds = cmds

    def __str__(self):
        if check_ivy(ivySelect):
            res = "after init{\n"
            for cmd in self.cmds:
                res += str(cmd)
            res += "}\n"
            pattern = r"\((.*?)\)"
            match = re.search(pattern, res)
            if match:
                lower_index = match.group(1)
                replacement = "(" + lower_index.upper() + ")"
                res = re.sub(re.escape(match.group(0)), replacement, res)
            return res
        else:
            res = "startstate \"%s\"\n" % self.name
            for cmd in self.cmds:
                res += indent(str(cmd), 2) + "\n"
            res += "endstartstate;"
            return res

    def __repr__(self):
        return "StartState(%s, %s)" % (repr(self.name), repr(self.cmds))

    def elaborate(self, prot, bound_vars):
        return StartState(self.name, [cmd.elaborate(prot, bound_vars) for cmd in self.cmds])


localVar = ""

class MurphiRuleSet:
    def __init__(self, var_decls, rule):
        self.var_decls = var_decls
        self.var_map = dict()
        for var_decl in self.var_decls:
            self.var_map[var_decl.name] = var_decl.typ
        self.rule = rule


    def __str__(self):
        if check_ivy(ivySelect):
            global localVar
            localVar = "%s\n" % (" ".join(str(var_decl) for var_decl in self.var_decls))
            localVar = re.sub(r"^\w+", "i_lv", localVar)
            res = str(self.rule)
            return res
        else:
            res = "ruleset %s do\n" % ("; ".join(str(var_decl) for var_decl in self.var_decls))
            res += str(self.rule) + "\n"
            res += "endruleset;"
            return res

    def __repr__(self):
        return "MurphiRuleSet(%s, %s)" % (repr(self.var_decls), repr(self.rule))

    def elaborate(self, prot, bound_vars):
        for var, typ in self.var_map.items():
            bound_vars[var] = typ
        res = MurphiRuleSet(self.var_decls, self.rule.elaborate(prot, bound_vars))
        for var in self.var_map:
            del bound_vars[var]
        return res

class MurphiRule:
    def __init__(self, name, cond, cmds):
        self.name = name
        self.cond = cond
        self.cmds = cmds

    def __str__(self):
        if check_ivy(ivySelect):
            # local_var = generate_random_letters(upper_or_lower="lower")
            res = "action %s = {\n" % self.name.lower()
            res += indent("local %s {\n" % (localVar), 4)
            match = re.search(r"\b\w+\b", localVar)
            # local_var = localVar[0]
            res += indent("assume " + str(self.cond) + ";", 4) + "\n"
            res = re.sub(r"\[([^]]+)\]", r"(\1)", res)
            for cmd in self.cmds:
                res += indent(str(cmd), 4 * 2) + "\n"
            res += indent("}", 4) + "\n}"
            split_strings = localVar.split("_", 1)
            original_name = split_strings[0]
            pattern = r"\(" + re.escape(original_name) + r"\)"
            res = re.sub(pattern, "(" + localVar.split(" ", 1)[0] + ")", res)
            return res
        else:
            res = "rule \"%s\"\n" % self.name
            res += indent(str(self.cond), 2) + "\n"
            res += "==>\n"
            res += "begin\n"
            for cmd in self.cmds:
                res += indent(str(cmd), 2) + "\n"
            res += "endrule;"
            return res

    def __repr__(self):
        return "MurphiRule(%s, %s, %s)" % (repr(self.name), repr(self.cond), repr(self.cmds))

    def __eq__(self, other):
        return isinstance(other, MurphiRule) and self.name == other.name and \
            self.cond == other.cond and self.cmds == other.cmds

    def elaborate(self, prot, bound_vars):
        return MurphiRule(self.name, self.cond.elaborate(prot, bound_vars),
                          [cmd.elaborate(prot, bound_vars) for cmd in self.cmds])

    def addSpecialGuard(self,f):
        self.cond = OpExpr("&",f,self.cond)

class MurphiInvariant:
    def __init__(self, name, inv):
        self.name = name
        self.inv = inv

    def __str__(self):
        if check_ivy(ivySelect):
            res = "conjecture " + str(self.inv)
            res = re.sub(r"\[([^]]+)\]", r"(\1)", res)
            return res
        else:
            res = "invariant \"%s\"\n" % self.name
            res += indent(str(self.inv), 2)
            res +=";\n"
            return res

    def __repr__(self):
        return "Invariant(%s, %s)" % (repr(self.name), repr(self.inv))

    def __eq__(self, other):
        return isinstance(other, MurphiInvariant) and self.name == other.name and \
            self.inv == other.inv

    def elaborate(self, prot, bound_vars):
        return MurphiInvariant(self.name, self.inv.elaborate(prot, bound_vars))

class MurphiProtocol:
    def __init__(self, consts, types, vars, start_state, decls):
        self.consts = consts
        self.types = types
        self.vars = vars
        self.start_state = start_state
        self.decls = decls
        global ivySelect
        self.invSelect = ivySelect

        self.typ_map = dict()
        self.enum_typ_map = dict()
        self.enum_map = dict()
        self.ori_enum_map = list()
        self.scalarset = list()
        # Process types
        if check_ivy(ivySelect):

            global record_map
            # self.record_map = dict()
            for typ_decl in self.types:
                typ_decl.name = typ_decl.name.lower() + "_t"
                if isinstance(typ_decl.typ, RecordType):
                    subrecordlist = list()
                    for subRecordTyp in typ_decl.typ.typ_decls:
                        subrecordlist.append([subRecordTyp.name, subRecordTyp.typ.name])
                        record_map[typ_decl.name] = subrecordlist
                    # print(subrecordlist)
                    # print("record_map:",record_map)
                if isinstance(typ_decl.typ, ScalarSetType):
                    self.scalarset.append(typ_decl.name)
                if isinstance(typ_decl.typ, EnumType):
                    for subname in typ_decl.typ.names:
                        self.ori_enum_map.append(subname)
                    typ_decl.typ.names = [item.lower() + "_em" for item in typ_decl.typ.names]
                    self.typ_map[typ_decl.name] = typ_decl.typ
                    self.enum_typ_map[typ_decl.name] = typ_decl.typ
                    for enum_val in typ_decl.typ.names:
                        self.enum_map[enum_val] = typ_decl.typ
                        # Process variables
            # print("record_map:",record_map)
            self.var_map = dict()
            for var_decl in self.vars:
                self.var_map[var_decl.name] = var_decl.typ
            self.var_map = {key.lower() + "_v": value for key, value in self.var_map.items()}
            # print(self.var_map)
            # Elaboration
            self.start_state = self.start_state.elaborate(self, dict())
            self.decls = [decl.elaborate(self, dict()) for decl in self.decls]
        else:
            # self.typ_map = dict()
            # self.enum_typ_map = dict()
            # self.enum_map = dict()
            for typ_decl in self.types:
                self.typ_map[typ_decl.name] = typ_decl.typ
                if isinstance(typ_decl.typ, EnumType):
                    self.enum_typ_map[typ_decl.name] = typ_decl.typ
                    for enum_val in typ_decl.typ.names:
                        self.enum_map[enum_val] = typ_decl.typ
                if isinstance(typ_decl.typ, ScalarSetType):
                    self.scalarset.append(typ_decl.name)

            # Process variables
            self.var_map = dict()
            for var_decl in self.vars:
                self.var_map[var_decl.name] = var_decl.typ

            # Elaboration
            self.start_state = self.start_state.elaborate(self, dict())
            self.decls = [decl.elaborate(self, dict()) for decl in self.decls]

        # Divide into categories
        self.rule_map = dict()
        self.ori_rule_map = dict()
        self.abs_rule_map = dict()
        self.inv_map = dict()
        self.ori_inv_map = dict()
        self.lemma_map = dict()


        for decl in self.decls:
            if isinstance(decl, MurphiRule):
                self.rule_map[decl.name] = decl
                if decl.name.startswith("ABS_"):
                    self.abs_rule_map[decl.name] = decl
                else:
                    self.ori_rule_map[decl.name] = decl
            elif isinstance(decl, MurphiRuleSet):
                self.rule_map[decl.rule.name] = decl
                if decl.rule.name.startswith("ABS_"):
                    self.abs_rule_map[decl.rule.name] = decl
                else:
                    self.ori_rule_map[decl.rule.name] = decl
            elif isinstance(decl, MurphiInvariant):
                self.inv_map[decl.name] = decl
                if decl.name.startswith("Lemma_"):
                    self.lemma_map[decl.name] = decl
                else:
                    self.ori_inv_map[decl.name] = decl
            else:
                raise NotImplementedError
        #refine abs_r_src etc
        self.export_name = list(self.rule_map.keys())
    def addition(self):
        for k in self.ori_rule_map.keys():
            r=self.ori_rule_map[k]
            if isinstance(r, MurphiRuleSet):
                if len(r.var_decls)==2:
                    for ak in self.abs_rule_map.keys():
                        if ak==("ABS_"+ k+ "_"+ r.var_decls[0].name ):
                            ar=self.abs_rule_map[ak]
                            addf=NegExpr(OpExpr("=",EnumValExpr(None,"Other"),VarExpr(name=r.var_decls[1].name,typ=r.var_decls[1].typ)))
                            ar.rule.addSpecialGuard(addf)
                        elif  ak==("ABS_"+k+"_"+r.var_decls[1].name):
                            ar=self.abs_rule_map[ak]
                            addf=NegExpr(OpExpr("=",VarExpr(name=r.var_decls[0].name,typ=r.var_decls[0].typ),EnumValExpr(None,"Other")))
                            ar.rule.addSpecialGuard(addf)
                        else:
                            pass



    def __str__(self):
        if check_ivy(self.invSelect):
            res = self.invSelect + "\n\n"
            for typ in self.types:
                if isinstance(typ.typ,RecordType):
                    pass
                else:
                    res += "type " + str(typ) + "\n\n"
            for var in self.vars:
                # print(var.typ)
                record_var_list = list()
                if isinstance(var.typ, ArrayType):
                    for key in record_map.keys():
                        # print(str(var.name))
                        if key in str(var.typ):
                            subvar_dict = dict()
                            for item in record_map[key]:
                                assert len(item)==2
                                # subvar = [var.name.lower()+"_v_"+item[0],item[1]]
                                subvar = var.name.lower() + "_v_" + item[0]

                                subvar_dict[item[0]] = subvar
                                subtyp = re.sub(key, item[1], str(var.typ))
                                # res += "individual " + subvar[0] + subtyp + "\n\n"
                                res += "individual " + subvar + subtyp + "\n\n"
                                record_var_list.append(subvar)
                            record_vars_map[var.name.lower()+"_v"] = subvar_dict
                    print("record_vars_map:",record_vars_map)
                else:
                    res += "individual " + str(var) + "\n\n"
            res += str(self.start_state) + "\n\n"
            for decl in self.decls:
                res += str(decl) + "\n\n"
            for name in self.export_name:
                res += "export " + name.lower() + "\n"
            return res
        else:
            res = "const\n\n"
            for const in self.consts:
                res += indent(str(const), 2) + ";\n\n"
            res += "type\n\n"
            for typ in self.types:
                res += indent(str(typ), 2) + ";\n\n"
            res += "var\n\n"
            for var in self.vars:
                res += indent(str(var), 2) + ";\n\n"
            res += str(self.start_state) + "\n\n"
            for decl in self.decls:
                res += str(decl) + "\n\n"
            return res

    # def getrule(self):
    #     return self.rule_map
        # return self.__str__()

    def __repr__(self):
        return "MurphiProtocol(%s, %s, %s, %s, %s)" % (repr(self.consts), repr(self.types), repr(self.vars), repr(self.start_state), repr(self.decls))
