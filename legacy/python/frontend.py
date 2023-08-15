import argparse
from llvmlite import ir
from z3 import *
import sys
import re


#### Translation ####

module = None
sys.setrecursionlimit(100000)


def bits_to_floating(bits):
    correspondence = {16: (5,11), 32: (8,24), 64: (11,53), 128: (15,113)}
    if isinstance(bits,int) or len(bits)==1:
        if bits in correspondence:
            bits = correspondence[bits]
    if bits == (5,11) or bits == [5,11]:
        return ir.HalfType()
    elif bits == (8,24) or bits == [8,24]:
        return ir.FloatType()
    elif bits == (11,53) or bits == [11,53]:
        return ir.DoubleType()
    elif bits == (15,113) or bits == [15,113]:
        raise Exception("Unsupported type FP128")
    else:
        raise Exception("Unsupported floating point type (only IEEE 16, 32 and 64 are supported)")

def floating_to_bits(type):
    return [(5,11),(8,24),(11,53),(15,113)][[ir.HalfType(),ir.FloatType(),ir.DoubleType()].index(type)]

def to_ll_type(smt_type):
    if is_fp_sort(smt_type):
        return bits_to_floating((smt_type.ebits(),smt_type.sbits()))
    elif smt_type==BoolSort():
        return ir.IntType(1)
    else:
        raise Exception("Unsupported type (only floating point and booleans supported)")

def ll_is_class(val, name, builder):
    return builder.call(get_intrinsic('class',val.type), [val,ir.Constant(ir.IntType(32),class_to_bits(name))])

def ll_is_zero(val, builder):
    return builder.icmp_unsigned("==",val,ir.Constant(val.type,0))

def ll_is_neg(val, builder):
    return builder.icmp_signed("<",val,ir.Constant(val.type,0))

def ll_is_posz(val,builder):
    return builder.icmp_signed(">=",val,ir.Constant(val.type,0))

def ll_urem(left,right, builder):
    return builder.select(ll_is_zero(right,builder),left,builder.urem(left,right))

def ll_smod(s,t, builder):
    zero = ir.Constant(s.type,0)
    #Check for t = 0 case
    u = ll_urem(builder.select(ll_is_neg(s,builder),builder.sub(zero,s),s),builder.select(ll_is_neg(t,builder),builder.sub(zero,t),t),builder)
    return builder.select(  ll_is_zero(u,builder), \
                            u, \
                            builder.select( builder.and_(ll_is_posz(s,builder),ll_is_posz(t,builder)), \
                                            u, \
                                            builder.select( builder.and_(ll_is_neg(s,builder),ll_is_posz(t,builder)), \
                                                            builder.add(builder.sub(zero,u),t), \
                                                            builder.select( builder.and_(ll_is_posz(s,builder),ll_is_neg(t,builder)), \
                                                                            builder.add(u,t), \
                                                                            builder.sub(zero,u)))))

def ll_repeat(val, times, builder):
    width = val.type.width
    newType = ir.IntType(times*width)
    if times == 1:
        return val
    else:
        current = builder.zext(val,ir.IntType(width*times))
        for i in range(1,times):
            current = builder.or_(current,builder.shl(builder.zext(val,newType),ir.Constant(newType,i*width)))
        return current

def to_bv_const(node):
    return ir.Constant(ir.IntType(node.size()),node.as_long())

def transform_name(name):
    return name.replace('=','_').replace('|','')

def get_fun_name(node):
    op_names = {
        258:    '=',
        259:    'distinct',
        260:    'ite',
        261:    'and',
        262:    'or',
        264:    'xor',
        265:    'not',
        266:    '=>',

        1024:   'bv',
        1027:   'bvneg',
        1028:   'bvadd',
        1029:   'bvsub',
        1030:   'bvmul',
        1031:   'bvsdiv',
        1032:   'bvudiv',
        1033:   'bvsrem',
        1034:   'bvurem',
        1035:   'bvsmod',
        1041:   'bvule',
        1042:   'bvsle',
        1043:   'bvuge',
        1044:   'bvsge',
        1045:   'bvult',
        1046:   'bvslt',
        1047:   'bvugt',
        1048:   'bvsgt',
        1049:   'bvand',
        1050:   'bvor',
        1051:   'bvnot',
        1052:   'bvxor',
        1053:   'bvnand',
        1054:   'bvnor',
        1055:   'bvxnor',
        1056:   'concat',
        1057:   'sign_extend',
        1058:   'zero_extend',
        1059:   'extract',
        1060:   'repeat',
        1063:   'bvcomp',
        1064:   'bvshl',
        1065:   'bvlshr',
        1066:   'bvashr',
        1067:   'rotate_left',
        1068:   'rotate_right',


        45062:  '+oo',
        45063:  '-oo',
        45064:  'NaN',
        45065:  '+zero',
        45066:  '-zero',
        45069:  'fneg',
        45067:  'fadd',
        45068:  'fsub',
        45070:  'fmul',
        45071:  'fdiv',
        45072:  'frem',
        45073:  'fabs',
        45074:  'fmin',
        45075:  'fmax',
        45076:  'fma',
        45077:  'sqrt',
        45079:  'feq',
        45080:  'flt',
        45081:  'fgt',
        45082:  'fleq',
        45083:  'fgeq',
        45084:  'nan',
        45085:  'infinite',
        45086:  'zero',
        45087:  'normal',
        45088:  'subnormal',
        45089:  'negative',
        45090:  'positive',
        45091:  'fp',
        45092:  'to_fp',
        45093:  'to_fp_unsigned',
        45094:  'fp.to_ubv',
        45095:  'fp.to_sbv',
        
        45101:  '!var'
    }
    return op_names[node.decl().kind()]


def ifun(node, name):
    try:
        return get_fun_name(node)==name
    except:
        return False

def class_to_bits(name):
    bits_dict = {
        'nan':          3,          #0000000011 = signalging nan, quiet nan
        'infinite':     516,        #1000000100 = signalging nan, quiet nan
        'zero':         96,         #0001100000 = negative zero, positive zero
        'normal':       264,        #0100001000 = negative normal, positive normal
        'subnormal':    144,        #0010010000 = negative subnormal, positive subnormal
        'negative':     60,         #0000111100 = neg infinity, neg normal, neg subnormal, neg zero
        'positive':     960         #1111000000 = pos infinity, pos normal, pos subnormal, pos zero
    }
    try:
        return bits_dict[name]
    except:
        raise Exception("Unsupported floating point class check: "+name)

def comp_to_str(name):
    op_dict = {
        'feq':          '==',
        'flt':          '<',
        'fgt':          '>',
        'fleq':         '<=',
        'fgeq':         '>=',
        'bvsle':        '<=',
        'bvsge':        '>=',
        'bvslt':        '<',
        'bvsgt':        '>',
        'bvule':        '<=',
        'bvuge':        '>=',
        'bvult':        '<',
        'bvugt':        '>'
    }
    try:
        return op_dict[name]
    except:
        raise Exception("Unsupported comparison: "+name)

#Does not include ==
def is_bv_signed_comparison(node):
    return get_fun_name(node) in ['bvsle', 'bvsge', 'bvslt', 'bvsgt']

#Does not include ==
def is_bv_unsigned_comparison(node):
    return get_fun_name(node) in ['bvule', 'bvuge', 'bvult', 'bvugt']

def is_bv_comparison(node):
    return node.children() and ((is_bv_sort(node.children()[0].sort()) and (ifun(node,'=') or ifun(node,'distinct')))  or is_bv_signed_comparison(node) or is_bv_unsigned_comparison(node))

def is_fp_comparison(node):
    return node.children() and (((node.children()[0].sort() in [Float16(),Float32(),Float64(),Float128()]) and (ifun(node,'=') or ifun(node,'distinct'))) or (get_fun_name(node) in ['feq', 'flt', 'fgt', 'fleq', 'fgeq']))

def is_class_check(node):
    return node.children() and (get_fun_name(node) in ['nan', 'infinite', 'zero', 'normal', 'subnormal', 'negative', 'positive'])


def build_formula(contents, builder, fun_args):
    #print("building formula "+str(contents))
    results = list(map(lambda a: build_constraint(a,builder,fun_args),contents))
    
    if len(results)==0:
        #An empty constraint
        return ir.Constant(ir.IntType(1),1)
    elif len(results)==1:
        return results[0]
    elif len(results)==2:
        return builder.and_(results[0],results[1])
    else:
        temp = results[0]
        for i in range(1,len(results)):
            temp = builder.and_(temp,results[i])
        return temp


def build_constraint(node, builder, fun_args):
    #print("building constraint "+str(node))

    if is_fp_comparison(node) or is_class_check(node):
        return build_fp_comparison(node,builder,fun_args)
    elif is_bv_comparison(node):
        return build_bv_comparison(node,builder,fun_args)
    elif not node.children():
        #Boolean leaf
        if is_const(node) and is_bool(node):
            if str(node)=='True':
                return ir.Constant(ir.IntType(1),1)
            elif str(node)=='False':
                return ir.Constant(ir.IntType(1),0)
            else:
                return fun_args[transform_name(str(node))]            
        else:
            raise Exception("Unexpected type for boolean leaf: "+str(node))
    else:
        results = list(map(lambda a: build_constraint(a,builder,fun_args),node.children()))

        if ifun(node,'and'):
            temp = results[0]
            for i in range(1,len(results)):
                temp = builder.and_(temp,results[i])
            return temp
        elif ifun(node,'or'):
            temp = results[0]
            for i in range(1,len(results)):
                temp = builder.or_(temp,results[i])
            return temp
        elif ifun(node,'xor'):
            temp = results[0]
            for i in range(1,len(results)):
                temp = builder.xor(temp,results[i])
            return temp
        elif ifun(node,'='):
            if len(results) == 2:
                return builder.icmp_unsigned("==",results[0],results[1])
            else:
                raise Exception("Unexpected number of arguments for boolean = (iff): "+str(node))
        elif ifun(node,'distinct'):
            if len(results) == 2:
                return builder.icmp_unsigned("!=",results[0],results[1])
            else:
                raise Exception("Unexpected number of arguments for boolean distinct: "+str(node))
        elif ifun(node,'=>'):
            if len(results)==2:
                temp = builder.not_(results[0])
                return builder.or_(temp,results[1])
            else:
                raise Exception("Unexpected number of arguments for implies: "+str(node))   
        elif ifun(node,'not'):
            if len(results) == 1:
                return builder.not_(results[0])
            else:
                raise Exception("Unexpected number of arguments for boolean not: "+str(node))
        elif ifun(node,'ite'):
            if len(results) == 3:
                return builder.select(results[0],results[1],results[2])
            else:
                raise Exception("Unexpected number of arguments for boolean ite: "+str(node))
        else:
            raise Exception("Unexpected constraint operation: "+str(node))

def build_fp_comparison(node, builder, fun_args):
    #print("buildling fp comparison "+str(node))
    left = build_fp_value(node.children()[0],builder,fun_args)
    if len(node.children())==2:
        right = build_fp_value(node.children()[1], builder, fun_args)

    #All comparisons are ordered (SMT-LIB says comparison is false if either argument is NaN)
    if ifun(node,'='):
        #Bitwise equality, except that all NaNs are equal
        iType = ir.IntType({ir.HalfType():16, ir.FloatType():32, ir.DoubleType():64}[left.type])
        lb = builder.bitcast(left,iType)
        rb = builder.bitcast(right,iType)
        return builder.or_(builder.and_(ll_is_class(left,'nan',builder),ll_is_class(right,'nan',builder)),builder.icmp_unsigned('==',lb,rb))
    elif ifun(node,'distinct'):
        #Bitwise inequality (not both NaNs, or bits are different)
        iType = ir.IntType({ir.HalfType():16, ir.FloatType():32, ir.DoubleType():64}[left.type])
        lb = builder.bitcast(left,iType)
        rb = builder.bitcast(right,iType)
        return builder.or_(builder.not_(builder.and_(ll_is_class(left,'nan',builder),ll_is_class(right,'nan',builder))),builder.icmp_unsigned('!=',lb,rb))
    elif is_fp_comparison(node):
        return builder.fcmp_ordered(comp_to_str(get_fun_name(node)),left,right)
    elif is_class_check(node):
        return ll_is_class(left, get_fun_name(node),builder)
    else:
        raise Exception("Unexpected floating point comparison operation: "+str(node))

def build_bv_comparison(node, builder, fun_args):
    #print("buildling bv comparison "+str(node))
    left = build_bv_value(node.children()[0],builder,fun_args)
    right = build_bv_value(node.children()[1], builder, fun_args)

    if ifun(node,'='):
        return builder.icmp_unsigned('==',left,right)
    elif ifun(node,'distinct'):
        return builder.icmp_unsigned('!=',left,right)
    elif is_bv_signed_comparison(node):
        return builder.icmp_signed(comp_to_str(get_fun_name(node)),left,right)
    elif is_bv_unsigned_comparison(node):
        return builder.icmp_unsigned(comp_to_str(get_fun_name(node)),left,right)
    else:
        raise Exception("Unexpected bitvector comparison operation: "+str(node))


def build_fp_value(node, builder, fun_args):
    #print("building fp value "+str(node))

    #Check that the rounding mode is suppored (only round to nearest in LLVM)
    if is_fprm(node):
        if node == RoundNearestTiesToEven():
            return None
        else:
            raise Exception("Unsupported fp rounding mode: "+str(node))

    #Floating point variables
    elif ifun(node,'!var'):
        return fun_args[transform_name(str(node))]
    #There are no floating point constants in SMT--all come from bitvectors

    #Tree case
    else:
        
        #Fixed floating point constants
        if ifun(node,'NaN'):
            return ir.Constant(to_ll_type(node.sort()),float("nan"))
        elif ifun(node,'-oo'):
            return ir.Constant(to_ll_type(node.sort()),float('-inf'))
        elif ifun(node,'+oo'):
            return ir.Constant(to_ll_type(node.sort()),float('-inf'))
        elif ifun(node,'-zero'):
            return ir.Constant(to_ll_type(node.sort()),-0.0)
        elif ifun(node,'+zero'):
            return ir.Constant(to_ll_type(node.sort()),0.0)
        elif ifun(node,'fp'):
            #Construct a floating point from 3 bitvectors (sign, exponent, significand)
            #Significand INCLUDES the hidden bit
            width = node.sort().sbits()+node.sort().ebits()
            
            parts = list(map(lambda a: builder.zext(build_bv_value(a,builder,fun_args),ir.IntType(width)),node.children()))
            
            sign = builder.shl(parts[0],ir.Constant(ir.IntType(width),width-1))
            exp = builder.shl(parts[1],ir.Constant(ir.IntType(width),node.sbits()-1))
            val = parts[2]
            
            return builder.bitcast(builder.or_(sign,builder.or_(exp,val)),bits_to_floating(width)) 
        
        elif ifun(node,'to_fp'):
            if len(node.children())==1:
                #bitcast conversion bv to fp
                res = build_bv_value(node.children()[0],builder,fun_args)
                return builder.bitcast(res,bits_to_floating(res.type.width))
            elif len(node.children())==2:
                if is_fp_sort(node.children()[1].sort()):
                    #Conversion from one fp type to another
                    newType = bits_to_floating(node.decl().params())
                    res = build_fp_value(node.children()[1],builder,fun_args)
                    if newType == res.type:
                        return res
                    elif sum(floating_to_bits(newType)) > sum(floating_to_bits(res.type)):
                        return builder.fpext(res,newType)
                    else:
                        return builder.fptrunc(res,newType)
                else:   
                    #Signed numeric conversion bv to fp
                    res = build_bv_value(node.children()[1],builder,fun_args)
                    return builder.sitofp(res,bits_to_floating(node.decl().params()))
            else:
                raise Exception("Unexpected number of arguments to to_fp conversion: "+str(node))
        elif ifun(node,'to_fp_unsigned'):
            res = build_bv_value(node.children()[1],builder,fun_args)
            return builder.uitofp(res,bits_to_floating(node.decl().params()))
        if ifun(node,'ite'):
            return builder.select(build_constraint(node.children()[0],builder,fun_args),build_fp_value(node.children()[1],builder,fun_args),build_fp_value(node.children()[2],builder,fun_args))



        results = list(map(lambda a: build_fp_value(a,builder,fun_args),node.children()))

        if ifun(node,'fabs'):
            return builder.call(get_intrinsic('fabs',results[0].type), [results[0]])
        elif ifun(node,'fneg'):
            return builder.fneg(results[0])
        elif ifun(node,'fadd'):
            #results[0] is the rounding mode
            return builder.fadd(results[1],results[2])
        elif ifun(node,'fsub'):
            return builder.fsub(results[1],results[2])
        elif ifun(node,'fmul'):
            return builder.fmul(results[1],results[2])
        elif ifun(node,'fdiv'):
            return builder.fdiv(results[1],results[2])
        elif ifun(node,'fma'):
            return builder.call(get_intrinsic('fma',results[1].type), [results[1],results[2],results[3]])
        elif ifun(node,'sqrt'):
            return builder.call(get_intrinsic('sqrt',results[1].type), [results[1]])
        elif ifun(node,'frem'):
            return builder.frem(results[0],results[1])
        elif ifun(node,'fmin'):
            return builder.call(get_intrinsic('min',results[0].type), [results[0],results[1]])
        elif ifun(node,'fmax'):
            return builder.call(get_intrinsic('max',results[0].type), [results[0],results[1]])
        else:
            raise Exception("Unexpected floating point value operation: "+str(node))

def build_bv_value(node, builder, fun_args):
    #print("building bv value "+str(node))
    
    #Bitvector constant
    if ifun(node,'bv'):
        return to_bv_const(node)

    #Symbol (variable)
    elif ifun(node,'!var'):
        return fun_args[transform_name(str(node))]

    #Tree case
    else:
        if ifun(node,'ite'):
            return builder.select(build_constraint(node.children()[0],builder,fun_args),build_bv_value(node.children()[1],builder,fun_args),build_bv_value(node.children()[2],builder,fun_args))
        elif ifun(node,'fp.to_ubv'):
            build_fp_value(node.children()[0]) #Need to check the rounding mode, even though the result is unused
            res = build_fp_value(node.children()[1], builder, fun_args)
            return builder.fptoui(res,ir.IntType(sum(floating_to_bits(node.size()))))
        elif ifun(node,'fp.to_sbv'):
            build_fp_value(node.children()[0], builder, fun_args) #Need to check the rounding mode, even though the result is unused
            res = build_fp_value(node.children()[1])
            return builder.fptosi(res,ir.IntType(sum(floating_to_bits(node.size()))))


        results = list(map(lambda a: build_bv_value(a,builder,fun_args),node.children()))

        if ifun(node,'bvneg'):
            return builder.sub(ir.Constant(results[0].type,0),results[0])
        elif ifun(node,'bvadd'):
            return builder.add(results[0],results[1])
        elif ifun(node,'bvsub'):
            return builder.sub(results[0],results[1])
        elif ifun(node,'bvmul'):
            return builder.mul(results[0],results[1])
        elif ifun(node,'bvsdiv'):
            return builder.select(ll_is_zero(results[1],builder),builder.select(ll_is_neg(results[0],builder),ir.Constant(results[0].type,1),ir.Constant(results[0].type,-1)),builder.sdiv(results[0],results[1]))
        elif ifun(node,'bvudiv'):
            return builder.select(ll_is_zero(results[1],builder),ir.Constant(results[0].type,-1),builder.udiv(results[0],results[1]))
        elif ifun(node,'bvsrem'):
            return builder.select(ll_is_zero(results[1],builder),results[0],builder.srem(results[0],results[1]))
        elif ifun(node,'bvurem'):
            return ll_urem(results[0],results[1],builder)
        elif ifun(node,'bvsmod'):
            return ll_smod(results[0],results[1],builder)
        elif ifun(node,'bvand'):
            return builder.and_(results[0],results[1])
        elif ifun(node,'bvor'):
            return builder.or_(results[0],results[1])
        elif ifun(node,'bvnot'):
            return builder.not_(results[0])
        elif ifun(node,'bvxor'):
            #bvxor is left associative (any number of arguments)
            temp = results[0]
            for i in range(1,len(results)):
                temp = builder.xor(temp,results[i])
            return temp
        elif ifun(node,'bvnand'):
            return builder.not_(builder.and_(results[0],results[1]))
        elif ifun(node,'bvnor'):
            return builder.not_(builder.or_(results[0],results[1]))
        elif ifun(node,'bvxnor'):
            return builder.not_(builder.xor(results[0],results[1]))
        elif ifun(node,'concat'):
            final_width = node.size()
            left = builder.zext(results[0],ir.IntType(final_width))
            right = builder.zext(results[1],ir.IntType(final_width))
            shifted = builder.shl(left,ir.Constant(ir.IntType(final_width),results[1].type.width))
            return builder.or_(right,shifted)
        elif ifun(node,'sign_extend'):
            return builder.sext(results[0],ir.IntType(node.size()))
        elif ifun(node,'zero_extend'):
            return builder.zext(results[0],ir.IntType(node.size()))
        elif ifun(node,'extract'):
            return builder.trunc(builder.lshr(results[0],ir.Constant(results[0].type,node.decl().params()[1])),ir.IntType(node.decl().params()[0]-node.decl().params()[1]+1))
        elif ifun(node,'repeat'):
            return ll_repeat(results[0],node.decl().params()[0],builder)
        elif ifun(node,'bvcomp'):
            return builder.icmp_unsigned("==",results[0],results[1])
        elif ifun(node,'bvshl'):
            #Check that the shift does not exceed the bit width to avoid LLVM undefined behavior
            return builder.select(builder.icmp_unsigned(">=",results[1],ir.Constant(results[0].type,node.size())),ir.Constant(results[0].type,0),builder.shl(results[0],results[1]))
        elif ifun(node,'bvlshr'):
            #Check for shift exceeding the bit width
            return builder.select(builder.icmp_unsigned(">=",results[1],ir.Constant(results[0].type,node.size())),ir.Constant(results[0].type,0),builder.lshr(results[0],results[1]))
        elif ifun(node,'bvashr'):
            #Check for shift exceeding the bit width
            return builder.select(builder.icmp_unsigned(">=",results[1],ir.Constant(results[0].type,node.size())),builder.select(ll_is_neg(results[0],builder),ir.Constant(results[0].type,-1),ir.Constant(results[0].type,0)),builder.ashr(results[0],results[1]))
        elif ifun(node,'rotate_left'):
            return builder.call(get_intrinsic('fshl',results[0].type), [results[0],results[0],ir.Constant(results[0].type,node.decl().params()[0]%node.size())])
        elif ifun(node,'rotate_right'):
            return builder.call(get_intrinsic('fshr',results[0].type), [results[0],results[0],ir.Constant(results[0].type,node.decl().params()[0]%node.size())])
        
        else:
            print(node.decl().kind())
            raise Exception("Unexpected bitvector value operation: "+str(node))   


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument('-s', '--smt',
                        help='Input .smt2 constraints',
                        required=True)
    parser.add_argument('-o', '--output',
                        help='Output .ll file',
                        required=False)

    args = parser.parse_args()
    return args

args = parse_args()
filename = args.smt


module = ir.Module(name=__file__)

fp_intrinsics = {
    'fabs':             list(map(lambda t: module.declare_intrinsic('llvm.fabs', [t]),[ir.HalfType(),ir.FloatType(),ir.DoubleType()])),
    'fma':              list(map(lambda t: module.declare_intrinsic('llvm.fma', [t,t,t]),[ir.HalfType(),ir.FloatType(),ir.DoubleType()])),
    'sqrt':             list(map(lambda t: module.declare_intrinsic('llvm.sqrt', [t]),[ir.HalfType(),ir.FloatType(),ir.DoubleType()])),
    'class':            list(map(lambda x: ir.Function(module,ir.FunctionType(ir.IntType(1),[x[0],ir.IntType(32)]), 'llvm.is.fpclass.f'+str(x[1])),[(ir.HalfType(),16),(ir.FloatType(),32),(ir.DoubleType(),64)])),
    'min':              list(map(lambda x: ir.Function(module,ir.FunctionType(x[0],[x[0],x[0]]), 'llvm.minnum.f'+str(x[1])),[(ir.HalfType(),16),(ir.FloatType(),32),(ir.DoubleType(),64)])),
    'max':              list(map(lambda x: ir.Function(module,ir.FunctionType(x[0],[x[0],x[0]]), 'llvm.maxnum.f'+str(x[1])),[(ir.HalfType(),16),(ir.FloatType(),32),(ir.DoubleType(),64)]))
}

bv_rols = dict()
bv_rors = dict()

def get_intrinsic(name,type):
    if str(type).startswith('i'):
        #Integer intrinsics
        width = int(str(type)[1:])
        if name=='fshl':
            if not (width in bv_rols):
                bv_rols[width] = ir.Function(module,ir.FunctionType(type,[type,type,type]),'llvm.fshl.i'+str(width))
            return bv_rols[width]
        elif name == 'fshr':
            if not (width in bv_rors):
                bv_rors[width] = ir.Function(module,ir.FunctionType(type,[type,type,type]),'llvm.fshr.i'+str(width))
            return bv_rors[width]
    else:
        #Floating point intrinsics
        pos = [ir.HalfType(),ir.FloatType(),ir.DoubleType()].index(type)
        return fp_intrinsics[name][pos]


ctx = z3.Context()
s = z3.Solver(ctx=ctx)
contents = z3.parse_smt2_file(filename)



#Parse variable declarations (Z3 parser doesn't do this transparently)
declared=[]

with open(filename, 'r') as file:
    declaration = re.compile(r'\(declare-fun\s(\|.*\||[\~\!\@\$\%\^\&\*\_\-\+\=\<\>\.\?\/A-Za-z0-9]+)\s*\(\s*\)\s*(\(\s*_\s*FloatingPoint\s*(\d+)\s*(\d+)\s*\)|Bool|\(\s*_\s*BitVec\s*(\d+)\s*\))\s*|declare-const\s(\|.*\||[\~\!\@\$\%\^\&\*\_\-\+\=\<\>\.\?\/A-Za-z0-9]+)\s*(\(\s*_\s*FloatingPoint\s*(\d+)\s*(\d+)\s*\)|Bool|\(\s*_\s*BitVec\s*(\d+)\s*\))\s*\)')
    sc = file.read()
    #SMTLIB type synonyms
    c = sc.replace('Float16','(_ FloatingPoint 5 11)')
    c = c.replace('Float32','(_ FloatingPoint 8 24)')
    c = c.replace('Float64','(_ FloatingPoint 11 53)')
    c = c.replace('Float128','(_ FloatingPoint 15 113)')
    matches = declaration.findall(c)
    for match in matches:
        if not match[0]:
            match = match[5:]
        else:
            match = match[:5]
            
        name = transform_name(match[0])
        if match[2]:
            #Floating point case
            declared.append((name,bits_to_floating((int(match[2]),int(match[3])))))
        elif match[4]:
            #Bitvector case
            declared.append((name,ir.IntType(int(match[4]))))
        else:
            #Boolean case
            declared.append((name,ir.IntType(1)))

# Declared symbols -> function arguments
argt = (x[1] for x in declared)
fnty = ir.FunctionType(ir.IntType(1),argt)
func = ir.Function(module,fnty,"smt")
for i in range(0,len(declared)):
    func.args[i].name = transform_name(declared[i][0])
fun_args = dict([(arg.name,arg) for arg in func.args])



block = func.append_basic_block()
builder = ir.IRBuilder(block)

result = build_formula(contents, builder, fun_args)

builder.ret(result)

if args.output:
    with open(args.output,'w') as file:
        file.write(str(module))
else:
    print(module)
