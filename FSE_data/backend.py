import argparse
from functools import *
from llvmlite import ir
import llvmlite.binding as llvm
from z3 import *
import struct

ROUNDING_MODE = RoundNearestTiesToEven()


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument('-l', '--llvm',
                        help='Input .ll file',
                        required=True)
    parser.add_argument('-o', '--output',
                        help='Output .smt2 file',
                        required=True)
    parser.add_argument('-s','--shiftToMultiply',nargs='?', const=True, default=False,
                        help='Include this flag to convert shift instructions with constant right argument to multiplication',
                        required=False)

    args = parser.parse_args()
    return args

#Instruction.get_name() function from llvmlite contains a bug on inputs like %0 and %1
def get_name(v):
    if ('=' in str(v)):
        return 'b'+str(v).strip().split(' ')[0].split('%')[1]
    elif v.name =="":
        if '%' in str(v):
            return 'b'+str(v).split('%')[1]
        else:
            return ''
    else:
        return 'b'+v.name


def get_operand(op, force_bv, smt_vars):
    if get_name(op) == '':
        stn = str(op).split(' ')[1]
        if str(op.type) == 'i1':
            return stn =='true'
        elif str(op.type).startswith('i'):
            val = int(stn)
            return BitVecVal(val,int(str(op.type)[1:])) if force_bv else val
        elif str(op.type) in ['half', 'float', 'double']:
            new_type = to_smt_type(op.type)
            hfd = [16,32,64,128].index(new_type.ebits()+new_type.sbits())
            if ('e+' in stn) or ('e-' in stn):
                #Interpret the exponential fp with Python's parser, convert the bits to an integer, and return a bitvector with that value
                
                val = struct.unpack(['H','I','Q'][hfd], struct.pack(['e','f','d'][hfd], float(stn)))[0]
            else:
                
                #Read the LLVM hex float constant as a python integer (always 64 bits based on LLVM)
                val = int(stn,16)
                #Bitcast to a python 64-bit floating point
                py_64fp = struct.unpack('d',struct.pack('Q',val))[0]
                #Convert 64-bit python floating point to appropriate size
                inter2 = struct.unpack(['e','f','d'][hfd],struct.pack(['e','f','d'][hfd],py_64fp))[0]
                #Bitcast correct size floating point back to integer of corresponding size
                val = struct.unpack(['H','I','Q'][hfd],struct.pack(['e','f','d'][hfd],inter2))[0]
            
            return fpBVToFP(BitVecVal(val,new_type.ebits()+new_type.sbits()),new_type)
        else:
            raise Exception("Unsupported operand type: "+str(op))
    else:
        return smt_vars[get_name(op)]

def to_smt_type(t):
    if str(t) == 'i1':
        return Bool()
    elif str(t).startswith("i"):
        return BitVecSort(int(str(t)[1:]))
    elif str(t) == 'half':
        return Float16()
    elif str(t) == 'float':
        return Float32()
    elif str(t) == 'double':
        return Float64()
    else:
        raise Exception("Unsupported LLVM type: " + str(v.type))

def to_smt_var(v):
    if str(v.type) == 'i1':
        return Bool(get_name(v))
    elif str(v.type).startswith("i"):
        return BitVec(get_name(v),int(str(v.type)[1:]))
    elif str(v.type) == 'half':
        return FP(get_name(v),Float16())
    elif str(v.type) == 'float':
        return FP(get_name(v),Float32())
    elif str(v.type) == 'double':
        return FP(get_name(v),Float64())
    else:
        raise Exception("Unsupported LLVM type: " + str(v.type))

def class_bits_to_fun(b):
    bits_dict = {
        3:      fpIsNaN,
        516:    fpIsInf,
        96:     fpIsZero,
        264:    fpIsNormal,
        144:    fpIsSubnormal,
        60:     fpIsNegative,
        960:    fpIsPositive
    }
    return bits_dict[b]

def interpret_fcmp(inst_str, val, left, right):
    name = inst_str.split('fcmp ')[1].split(' ')[0]
    if name == "false":
        sol.add(val == False)
    elif name == "oeq":
        sol.add(val == fpEQ(left,right))
    elif name == "ogt":
        sol.add(val == fpGT(left,right))
    elif name == "oge":
        sol.add(val == fpGEQ(left,right))
    elif name == "olt":
        sol.add(val == fpLT(left,right))
    elif name == "ole":
        sol.add(val == fpLEQ(left,right))
    elif name == "one":
        sol.add(val == And(Not(fpIsNaN(left)),Not(fpIsNaN(right),Not(fpEQ(left,right)))))
    elif name == "ord":
        sol.add(val == And(Not(fpIsNaN(left)),Not(fpIsNaN(right))))
    elif name == "ueq":
        sol.add(val == Or(fpIsNaN(left),fpIsNaN(right),fpEQ(left,right)))
    elif name == "ugt":
        sol.add(val == Or(fpIsNaN(left),fpIsNaN(right),fpGT(left,right)))
    elif name == "uge":
        sol.add(val == Or(fpIsNaN(left),fpIsNaN(right),fpGEQ(left,right)))
    elif name == "ult":
        sol.add(val == Or(fpIsNaN(left),fpIsNaN(right),fpLT(left,right)))
    elif name == "ule":
        sol.add(val == Or(fpIsNaN(left),fpIsNaN(right),fpLEQ(left,right)))
    elif name == "une":
        sol.add(val == Or(fpIsNaN(left),fpIsNaN(right),Not(fpEQ(left,right))))
    elif name == "uno":
        sol.add(val == Or(fpIsNaN(left),fpIsNaN(right)))
    elif name == "true":
        sol.add(val == True)
    else:
        raise Exception("Badly formed FCMP instruction (only ordered comparisons supported): " + inst_str)


def interpret_bv_icmp(inst_str, val, left, right, altl=None):
    #Optional argument altl is for the case where both left and right are constants
    name = inst_str.split('icmp ')[1].split(' ')[0]
    if name == "eq":
        sol.add(val == (left == right))
    elif name == "ne":
        sol.add(val == (left != right))
    elif name == "ugt":
        sol.add(val == UGT(altl if altl else left,right))
    elif name == "uge":
        sol.add(val == UGE(altl if altl else left,right))
    elif name == "ult":
        sol.add(val == ULT(altl if altl else left,right))
    elif name == "ule":
        sol.add(val == ULE(altl if altl else left,right))
    elif name == "sgt":
        sol.add(val == (left > right))
    elif name == "sge":
        sol.add(val == (left >= right))
    elif name == "slt":
        sol.add(val == (left < right))
    elif name == "sle":
        sol.add(val == (left <= right))
    else:
            raise Exception("Badly formed ICMP instruction for bitvectors: " + inst_str)

def interpret_bool_icmp(inst_str, val, left, right):
    name = inst_str.split('icmp ')[1].split(' ')[0]
    if name == "eq":
        sol.add(val == (left == right))
    elif name == "ne":
        sol.add(val == (left != right))
    else:
        raise Exception("Badly formed ICMP instruction for booleans: " + inst_str)
    


args = parse_args()

sol = Solver()

with open(args.llvm) as f:
    llvm_ir = f.read()




mod = llvm.parse_assembly(llvm_ir)
mod.verify()

fun = mod.get_function("smt")
llvm_vars = fun.arguments
smt_vars = {}
blocks = list(fun.blocks)

for var in llvm_vars:
    smt_vars[get_name(var)] = to_smt_var(var)


for block in blocks:
    insts = list(block.instructions)
    i = 0
    #Must use a concrete loop counter because some instructions skip over the next
    while i < len(insts):
        inst = insts[i]
        #Handle the return instruction
        if (inst.opcode == "ret"):
            sol.add(get_operand(list(inst.operands)[0],False, smt_vars))

        else:
            #umul.with.overflow is a special instruction which produces a vector
            #In SMT translation, we only ever deal with the second element of that vector, so we don't make it a variable
            if (not "umul.with.overflow" in str(inst)):
                if (not get_name(inst) in smt_vars.keys()):
                    smt_vars[get_name(inst)] = to_smt_var(inst)
                new_var = smt_vars[get_name(inst)]

            #Handle llvm intrinsics
            if (inst.opcode == "call"):
                intrinsic = list(inst.operands)[-1].name[5:]
                #Floating point intrinsics
                if intrinsic.startswith("fabs"):
                    arg = get_operand(list(inst.operands)[0],False, smt_vars)
                    sol.add(new_var == fpAbs(arg))
                elif intrinsic.startswith("fma"):
                    a = get_operand(list(inst.operands)[0], False, smt_vars)
                    b = get_operand(list(inst.operands)[1], False, smt_vars)
                    c = get_operand(list(inst.operands)[2], False, smt_vars)
                    sol.add(new_var == fpFMA(ROUNDING_MODE,a,b,c))
                elif intrinsic.startswith("sqrt"):
                    arg = get_operand(list(inst.operands)[0], False, smt_vars)
                    sol.add(new_var == fpSqrt(ROUNDING_MODE,arg))
                elif intrinsic.startswith("minnum"):
                    left = get_operand(list(inst.operands)[0], False, smt_vars)
                    right = get_operand(list(inst.operands)[1], False, smt_vars)
                    sol.add(new_var == fpMin(left,right))
                elif intrinsic.startswith("maxnum"):
                    left = get_operand(list(inst.operands)[0], False, smt_vars)
                    right = get_operand(list(inst.operands)[1], False, smt_vars)
                    sol.add(new_var == fpMax(left,right))
                elif intrinsic.startswith("is.fpclass"):
                    arg = get_operand(list(inst.operands)[0], False, smt_vars)
                    bitmask = int(str(list(inst.operands)[1]).split(' ')[1])
                    fun = class_bits_to_fun(bitmask)
                    sol.add(new_var == fun(arg))
                #Bitvector intrinsics
                elif intrinsic.startswith("bswap"):
                    arg = get_operand(list(inst.operands)[0],True,smt_vars)
                    width = int(str(inst.type)[1:])
                    bytes = [ Extract(width-(8*i)-1, width-(8*(i+1)), arg) for i in range((width//8)-1,-1,-1) ]
                    sol.add(new_var == Concat(bytes))
                elif intrinsic.startswith("ctpop"):
                    arg = get_operand(list(inst.operands)[0],True,smt_vars)
                    width = int(str(inst.type)[1:])
                    bits = [ ZeroExt(width-1,Extract(i, i, arg)) for i in range(0,width) ]
                    sol.add(new_var == reduce(lambda a, b: a + b, bits))
                elif intrinsic.startswith("bitreverse"):
                    arg = get_operand(list(inst.operands)[0],True,smt_vars)
                    width = int(str(inst.type)[1:])
                    bits = [ Extract(i, i, arg) for i in range(width-1,-1,-1) ]
                    sol.add(new_var == Concat(bits))
                elif intrinsic.startswith("abs"):
                    arg = get_operand(list(inst.operands)[0],False,smt_vars)
                    width = int(str(inst.type)[1:])
                    sol.add(new_var == If(arg < 0,-arg,arg))
                elif intrinsic.startswith("fshl"):
                    left = get_operand(list(inst.operands)[0],False,smt_vars)
                    right = get_operand(list(inst.operands)[1],False,smt_vars)
                    shamt = get_operand(list(inst.operands)[2],False,smt_vars)
                    width = int(str(inst.type)[1:])
                    sol.add(new_var == Extract((width*2)-1,width,Concat(left,right) << shamt))
                elif intrinsic.startswith("fshr"):
                    left = get_operand(list(inst.operands)[0],False,smt_vars)
                    right = get_operand(list(inst.operands)[1],False,smt_vars)
                    shamt = get_operand(list(inst.operands)[2],False,smt_vars)
                    width = int(str(inst.type)[1:])
                    sol.add(new_var == Extract(width-1,0,Concat(left,right) >> shamt))
                elif intrinsic.startswith("usub.sat"):
                    left = get_operand(list(inst.operands)[0],False,smt_vars)
                    right = get_operand(list(inst.operands)[1],False,smt_vars)
                    width = int(str(inst.type)[1:])
                    sol.add(new_var == If(ULE(left,right),0,left-right))
                elif intrinsic.startswith("umin"):
                    left = get_operand(list(inst.operands)[0],False,smt_vars)
                    right = get_operand(list(inst.operands)[1],False,smt_vars)
                    sol.add(new_var == If(ULE(left,right),left,right))
                elif intrinsic.startswith("umax"):
                    left = get_operand(list(inst.operands)[0],False,smt_vars)
                    right = get_operand(list(inst.operands)[1],False,smt_vars)
                    sol.add(new_var == If(ULE(left,right),right,left))
                elif intrinsic.startswith("smin"):
                    left = get_operand(list(inst.operands)[0],False,smt_vars)
                    right = get_operand(list(inst.operands)[1],False,smt_vars)
                    sol.add(new_var == If(left <= right,left,right))
                elif intrinsic.startswith("smax"):
                    left = get_operand(list(inst.operands)[0],False,smt_vars)
                    right = get_operand(list(inst.operands)[1],False,smt_vars)
                    sol.add(new_var == If(left <= right,right,left))
                elif intrinsic.startswith("umul.with.overflow"):
                    if (insts[i+1].opcode=="extractvalue") and (str(insts[i+1])[-1]=='1'):
                        left = get_operand(list(inst.operands)[0],False,smt_vars)
                        right = get_operand(list(inst.operands)[1],False,smt_vars)
                        smt_vars[get_name(insts[i+1])] = to_smt_var(insts[i+1])
                        sol.add(smt_vars[get_name(insts[i+1])] == If(Or(left==0,right==0),False,Not(((left*right)/left)==right)))
                        i+=1
                else:
                    raise Exception("Unsupported LLVM intrinsic: "+str(inst))

            elif len(list(inst.operands)) == 1:
                arg = get_operand(list(inst.operands)[0],True,smt_vars)
                #Only one unary floating point instruction
                if (inst.opcode == "fneg"):
                    sol.add(new_var == fpNeg(arg))
                elif (inst.opcode == 'fptoui'):
                    sol.add(new_var == fpToUBV(ROUNDING_MODE,arg,BitVecSort(arg.ebits()+arg.sbits())))
                elif (inst.opcode == 'fptosi'):
                    sol.add(new_var == fpToSBV(ROUNDING_MODE,arg,BitVecSort(arg.ebits()+arg.sbits())))
                elif (inst.opcode == 'fpext') or (inst.opcode == 'fptrunc'):
                    sol.add(new_var == fpFPToFP(ROUNDING_MODE,arg,to_smt_type(inst.type)))
                else:
                    #Unary bitvector operations
                    if not (inst.opcode in ['sitofp','uitofp','bitcast']):
                        #Not an integer return type for these two conversion instructions
                        width = int(str(inst.type)[1:])
                    if (inst.opcode == "trunc"):
                        sol.add(new_var == Extract(width-1,0,arg))
                    elif (inst.opcode == "zext"):
                        if (is_bool(arg)):
                            #Special case: the optimizer introduces a zext i1 ..., which needs to be an integer in SMT
                            sol.add(new_var == ZeroExt(width-int(str(list(inst.operands)[0].type)[1:]),If(arg,BitVecVal(1,1),BitVecVal(0,1))))
                        else:
                            sol.add(new_var == ZeroExt(width-int(str(list(inst.operands)[0].type)[1:]),arg))
                    elif (inst.opcode == "sext"):
                        if (is_bool(arg)):
                            #Special case: the optimizer introduces a sext i1 ..., which needs to be an integer in SMT
                            sol.add(new_var == SignExt(width-int(str(list(inst.operands)[0].type)[1:]),If(arg,BitVecVal(1,1),BitVecVal(0,1))))
                        else:
                            sol.add(new_var == SignExt(width-int(str(list(inst.operands)[0].type)[1:]),arg))
                    elif (inst.opcode == "freeze"):
                        #Frontend always introduces a check for divisions by 0, so all freeze instructions are guaranteed to return their argument
                        sol.add(new_var == arg)
                    elif (inst.opcode == "bitcast"):
                        if str(inst.type) in ['half', 'float', 'double']:
                            sol.add(new_var == fpBVToFP(arg,to_smt_type(inst.type)))
                        else:
                            #There is no FP -> BV bitcast equivalent in SMT since NaN has multiple representations
                            #So convert the new variable into a floating and constrain them to be equal
                            new_type = [Float16(),Float32(),Float64()][[16,32,64].index(int(str(inst.type)[1:]))]
                            sol.add(fpBVToFP(new_var,new_type) == arg)
                            
                    elif (inst.opcode == "sitofp"):
                        sol.add(new_var == fpSignedToFP(ROUNDING_MODE,arg,to_smt_type(inst.type)))
                    elif (inst.opcode == "uitofp"):
                        sol.add(new_var == fpToFPUnsigned(ROUNDING_MODE,arg,to_smt_type(inst.type)))
                    else:
                        raise Exception("Unsupported LLVM instruction on one argument: "+str(inst))
            elif len(list(inst.operands)) == 2:
                left = get_operand(list(inst.operands)[0], False, smt_vars)
                right = get_operand(list(inst.operands)[1], False, smt_vars)
                
                #Boolean case
                if (is_bool(left) or isinstance(left,bool)) and (is_bool(right) or isinstance(right,bool)):
                    if (inst.opcode == "and"):
                        sol.add(new_var == And(left,right))
                    elif (inst.opcode == "or"):
                        sol.add(new_var == Or(left,right))
                    elif (inst.opcode == "xor"):
                        sol.add(new_var == Xor(left,right))
                    elif (inst.opcode == "icmp"):
                        interpret_bool_icmp(str(inst),new_var,left,right)
                    else:
                        raise Exception("Unsupported LLVM instruction on booleans: "+str(inst))
                #FloatingPoint case
                elif is_fp(left) and is_fp(right):
                    if (inst.opcode == "fadd"):
                        sol.add(new_var == fpAdd(ROUNDING_MODE,left,right))
                    elif (inst.opcode == "fsub"):
                        sol.add(new_var == fpSub(ROUNDING_MODE,left,right))
                    elif (inst.opcode == "fmul"):
                        sol.add(new_var == fpMul(ROUNDING_MODE,left,right))
                    elif (inst.opcode == "fdiv"):
                        sol.add(new_var == fpDiv(ROUNDING_MODE,left,right))
                    elif (inst.opcode == "frem"):
                        sol.add(new_var == fpRem(ROUNDING_MODE,left,right))
                    elif (inst.opcode == "fcmp"):
                        interpret_fcmp(str(inst),new_var,left,right)
                    else:
                        raise Exception("Unsupported LLVM floating point instruction: "+str(inst))
                #Bitvector case
                else:
                    if (inst.opcode == "shl"):
                        if (args.shiftToMultiply and isinstance(right,int)):
                            #Convert shift by a constant to a multiplication
                            sol.add(new_var == left * (2**right))
                        else:
                            sol.add(new_var == (left << right))
                    elif (inst.opcode == "lshr"):
                        #The left operand must be forced to be a bitvector
                        sol.add(new_var == LShR(get_operand(list(inst.operands)[0], True, smt_vars),right))
                    elif (inst.opcode == "ashr"):
                        #Shift right is not equivalent to division
                        sol.add(new_var == left >> right)
                    elif (inst.opcode == "and"):
                        sol.add(new_var == (left & right))
                    elif (inst.opcode == "or"):
                        sol.add(new_var == (left | right))
                    elif (inst.opcode == "sub"):
                        sol.add(new_var == (left - right))
                    elif (inst.opcode == "add"):
                        sol.add(new_var == (left + right))
                    elif (inst.opcode == "mul"):
                        sol.add(new_var == (left * right))
                    elif (inst.opcode == "sdiv"):
                        sol.add(new_var == (left / right))
                    elif (inst.opcode == "udiv"):
                        sol.add(new_var == UDiv(left, right))
                    elif (inst.opcode == "urem"):
                        sol.add(new_var == URem(left,right))
                    elif (inst.opcode == "srem"):
                        sol.add(new_var == SRem(left,right))
                    elif (inst.opcode == "xor"):
                        sol.add(new_var == (left ^ right))
                    elif (inst.opcode == "icmp"):
                        if isinstance(left,int) and isinstance(right,int):
                            interpret_bv_icmp(str(inst), new_var, left, right, get_operand(list(inst.operands)[0], True, smt_vars))
                        else:
                            interpret_bv_icmp(str(inst), new_var, left, right)
                    else:
                        raise Exception("Unsupported LLVM bitvector instruction: "+str(inst))
                    
            elif len(list(inst.operands)) == 3:
                if (inst.opcode == "select"):
                    #Handles select on boolean, bitvectors, and fp
                    cond = get_operand(list(inst.operands)[0], False, smt_vars)
                    left = get_operand(list(inst.operands)[1], False, smt_vars)
                    right = get_operand(list(inst.operands)[2], False, smt_vars)
                    if isinstance(left,int) and isinstance(right,int):
                        left = get_operand(list(inst.operands)[1], True, smt_vars)
                    sol.add(new_var==If(cond,left,right))
                else:
                    raise Exception("Unsupported LLVM instruction on 3 arguments: "+str(inst))
            else:
                raise Exception("Unexpected number of arguments: "+str(inst))
        i+=1



filename = args.output
with open(filename, mode='w') as f:
    f.write(sol.to_smt2())