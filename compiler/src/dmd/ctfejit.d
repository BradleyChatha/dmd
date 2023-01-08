/**
 * The entry point for CTFE.
 *
 * Specification: ($LINK2 https://dlang.org/spec/function.html#interpretation, Compile Time Function Execution (CTFE))
 *
 * Copyright:   Copyright (C) 1999-2023 by The D Language Foundation, All Rights Reserved
 * Authors:     $(LINK2 https://www.digitalmars.com, Walter Bright)
 * License:     $(LINK2 https://www.boost.org/LICENSE_1_0.txt, Boost License 1.0)
 * Source:      $(LINK2 https://github.com/dlang/dmd/blob/master/src/dmd/dinterpret.d, _dinterpret.d)
 * Documentation:  https://dlang.org/phobos/dmd_dinterpret.html
 * Coverage:    https://codecov.io/gh/dlang/dmd/src/master/src/dmd/dinterpret.d
 */

module dmd.ctfejit;

import dmd.root.array;
import dmd.apply;
import dmd.arraytypes;
import dmd.astenums;
import dmd.attrib;
import dmd.builtin;
import dmd.constfold;
import dmd.ctfeexpr;
import dmd.dclass;
import dmd.declaration;
import dmd.dstruct;
import dmd.dsymbol;
import dmd.dsymbolsem;
import dmd.dtemplate;
import dmd.errors;
import dmd.expression;
import dmd.expressionsem;
import dmd.func;
import dmd.globals;
import dmd.hdrgen;
import dmd.id;
import dmd.identifier;
import dmd.init;
import dmd.initsem;
import dmd.location;
import dmd.mtype;
import dmd.printast;
import dmd.root.rmem;
import dmd.root.array;
import dmd.root.ctfloat;
import dmd.root.region;
import dmd.root.rootobject;
import dmd.root.utf;
import dmd.statement;
import dmd.tokens;
import dmd.visitor;

// BOOKMARK: Public interface
Expression ctfeInterpret2(Expression exp, scope ref CTFEVirtualMachine vm = g_ctfeVirtualMachine)
out(v) { import std; writeln(":: ctfeInterpret2\n", "    exp: ", exp, "\n    value: ", v); }
do
{
    CTFEFunctionInfo info;
    CTFEValue result;
    if(!compileExpressionAsFunction(exp, vm, info))
        return CTFEExp.cantexp;
    executeFunction(info, result, vm);

    final switch(result.type) with(CTFEValue.Type)
    {
        case i8Bool: return IntegerExp.create(exp.loc, cast(dinteger_t)result.value.i8Bool, Type.tbool);
        case i8:    return IntegerExp.create(exp.loc, result.value.i8, Type.tint8);
        case i16:   return IntegerExp.create(exp.loc, result.value.i16, Type.tint16);
        case i32:   return IntegerExp.create(exp.loc, result.value.i32, Type.tint32);
        case i64:   return IntegerExp.create(exp.loc, result.value.i64, Type.tint64);
        case u8:    return IntegerExp.create(exp.loc, result.value.u8, Type.tuns8);
        case u16:   return IntegerExp.create(exp.loc, result.value.u16, Type.tuns16);
        case u32:   return IntegerExp.create(exp.loc, result.value.u32, Type.tuns32);
        case u64:   return IntegerExp.create(exp.loc, result.value.u64, Type.tuns64);
        case funcPointer:
        case startOfFrame:
        case funcContext:
        case localSlotRef:
        case typePtr:
            return CTFEExp.cantexp;
    }
}

// BOOKMARK: Instruction Descriptors
private struct Pops 
{ 
    size_t amount; 
    bool dynamic; 
}

private struct Pushes 
{ 
    size_t amount; 
    bool dynamic; 
}

private struct BinaryArith(alias T)
{
    alias Type = T; 
    char operation; 
}

private struct Load(alias T)
{
    alias Type = T;
}

private struct Convert(alias FromT, alias ToT)
{
    alias From = FromT;
    alias To = ToT;
}

// BOOKMARK: Data Structures
private enum SMALL_ARG_ARRAY_SIZE = 8;

extern(C++) struct CTFEFunctionInfo
{
    static __gshared Dsymbol[] contextPointerSymbolCache;

    size_t opcodeStartIndex;
    size_t opcodeEndIndex;
    size_t[Dsymbol] localSlotIndexMap;

    bool hasBeenGenerated()
    {
        return this.opcodeEndIndex > 0;
    }

    size_t getLocalSlotIndex(scope Dsymbol var)
    {
        auto ptr = var in this.localSlotIndexMap;
        if(ptr !is null)
            return *ptr;

        auto index = this.localSlotIndexMap.length;
        this.localSlotIndexMap[var] = index;
        return index;
    }

    size_t* tryGetLocalSlotIndex(scope Dsymbol var)
    {
        auto ptr = (var in this.localSlotIndexMap);
        return ptr;
    }

    Dsymbol getAnonymousSymbolForContextPointer(size_t index)
    {
        while(index >= contextPointerSymbolCache.length)
            contextPointerSymbolCache ~= new Dsymbol(new Identifier("__ctfe_context_pointer"));
        return contextPointerSymbolCache[index];
    }
}

private struct CTFEOpcode
{
    enum Instruction : ubyte
    {
        // Uncategorised
        @Pops(0) @Pushes(0) nop,
        @Pops(0, true) @Pushes(0, true) call,
        @Pops(0, true) @Pushes(0, true) ret,

        // Stack Manipulation
        @Pops(0) @Pushes(1) copy_frel,

        // Local Manipulation
        @Pops(1) @Pushes(0) local_store,
        @Pops(0) @Pushes(1) local_load,
        @Pops(1) @Pushes(0) local_store_ind,
        @Pops(0) @Pushes(1) local_load_ind,

        // Direct loads
        @Pops(0) @Pushes(1) @(Load!bool) ld_i8Bool,
        @Pops(0) @Pushes(1) @(Load!byte) ld_i8,
        @Pops(0) @Pushes(1) @(Load!short) ld_i16,
        @Pops(0) @Pushes(1) @(Load!int) ld_i32,
        @Pops(0) @Pushes(1) @(Load!long) ld_i64,
        @Pops(0) @Pushes(1) @(Load!ubyte) ld_u8,
        @Pops(0) @Pushes(1) @(Load!ushort) ld_u16,
        @Pops(0) @Pushes(1) @(Load!uint) ld_u32,
        @Pops(0) @Pushes(1) @(Load!ulong) ld_u64,
        @Pops(0) @Pushes(1) ld_func_ctx,

        // Primitive conversion functions
        @Pops(1) @Pushes(1) @(Convert!(byte, short)) cvt_i8_16,
        @Pops(1) @Pushes(1) @(Convert!(byte, int)) cvt_i8_32,
        @Pops(1) @Pushes(1) @(Convert!(byte, long)) cvt_i8_64,
        @Pops(1) @Pushes(1) @(Convert!(short, byte)) cvt_i16_8,
        @Pops(1) @Pushes(1) @(Convert!(short, int)) cvt_i16_32,
        @Pops(1) @Pushes(1) @(Convert!(short, long)) cvt_i16_64,
        @Pops(1) @Pushes(1) @(Convert!(int, byte)) cvt_i32_8,
        @Pops(1) @Pushes(1) @(Convert!(int, short)) cvt_i32_16,
        @Pops(1) @Pushes(1) @(Convert!(int, long)) cvt_i32_64,
        @Pops(1) @Pushes(1) @(Convert!(long, byte)) cvt_i64_8,
        @Pops(1) @Pushes(1) @(Convert!(long, short)) cvt_i64_16,
        @Pops(1) @Pushes(1) @(Convert!(long, int)) cvt_i64_32,

        @Pops(1) @Pushes(1) @(Convert!(ubyte, ushort)) cvt_u8_16,
        @Pops(1) @Pushes(1) @(Convert!(ubyte, uint)) cvt_u8_32,
        @Pops(1) @Pushes(1) @(Convert!(ubyte, ulong)) cvt_u8_64,
        @Pops(1) @Pushes(1) @(Convert!(ushort, ubyte)) cvt_u16_8,
        @Pops(1) @Pushes(1) @(Convert!(ushort, uint)) cvt_u16_32,
        @Pops(1) @Pushes(1) @(Convert!(ushort, ulong)) cvt_u16_64,
        @Pops(1) @Pushes(1) @(Convert!(uint, ubyte)) cvt_u32_8,
        @Pops(1) @Pushes(1) @(Convert!(uint, ushort)) cvt_u32_16,
        @Pops(1) @Pushes(1) @(Convert!(uint, ulong)) cvt_u32_64,
        @Pops(1) @Pushes(1) @(Convert!(ulong, ubyte)) cvt_u64_8,
        @Pops(1) @Pushes(1) @(Convert!(ulong, ushort)) cvt_u64_16,
        @Pops(1) @Pushes(1) @(Convert!(ulong, uint)) cvt_u64_32,

        @Pops(1) @Pushes(1) cvt_u_i,
        @Pops(1) @Pushes(1) cvt_i_u,

        // Arithmetic
        @Pops(2) @Pushes(1) @(BinaryArith!byte('+')) add_i8,
        @Pops(2) @Pushes(1) @(BinaryArith!short('+')) add_i16,
        @Pops(2) @Pushes(1) @(BinaryArith!int('+')) add_i32,
        @Pops(2) @Pushes(1) @(BinaryArith!long('+')) add_i64,
        @Pops(2) @Pushes(1) @(BinaryArith!ubyte('+')) add_u8,
        @Pops(2) @Pushes(1) @(BinaryArith!ushort('+')) add_u16,
        @Pops(2) @Pushes(1) @(BinaryArith!uint('+')) add_u32,
        @Pops(2) @Pushes(1) @(BinaryArith!ulong('+')) add_u64,

        @Pops(2) @Pushes(1) @(BinaryArith!byte('/')) div_i8,
        @Pops(2) @Pushes(1) @(BinaryArith!short('/')) div_i16,
        @Pops(2) @Pushes(1) @(BinaryArith!int('/')) div_i32,
        @Pops(2) @Pushes(1) @(BinaryArith!long('/')) div_i64,
        @Pops(2) @Pushes(1) @(BinaryArith!ubyte('/')) div_u8,
        @Pops(2) @Pushes(1) @(BinaryArith!ushort('/')) div_u16,
        @Pops(2) @Pushes(1) @(BinaryArith!uint('/')) div_u32,
        @Pops(2) @Pushes(1) @(BinaryArith!ulong('/')) div_u64,

        @Pops(2) @Pushes(1) @(BinaryArith!byte('*')) mul_i8,
        @Pops(2) @Pushes(1) @(BinaryArith!short('*')) mul_i16,
        @Pops(2) @Pushes(1) @(BinaryArith!int('*')) mul_i32,
        @Pops(2) @Pushes(1) @(BinaryArith!long('*')) mul_i64,
        @Pops(2) @Pushes(1) @(BinaryArith!ubyte('*')) mul_u8,
        @Pops(2) @Pushes(1) @(BinaryArith!ushort('*')) mul_u16,
        @Pops(2) @Pushes(1) @(BinaryArith!uint('*')) mul_u32,
        @Pops(2) @Pushes(1) @(BinaryArith!ulong('*')) mul_u64,

        @Pops(2) @Pushes(1) @(BinaryArith!byte('-')) sub_i8,
        @Pops(2) @Pushes(1) @(BinaryArith!short('-')) sub_i16,
        @Pops(2) @Pushes(1) @(BinaryArith!int('-')) sub_i32,
        @Pops(2) @Pushes(1) @(BinaryArith!long('-')) sub_i64,
        @Pops(2) @Pushes(1) @(BinaryArith!ubyte('-')) sub_u8,
        @Pops(2) @Pushes(1) @(BinaryArith!ushort('-')) sub_u16,
        @Pops(2) @Pushes(1) @(BinaryArith!uint('-')) sub_u32,
        @Pops(2) @Pushes(1) @(BinaryArith!ulong('-')) sub_u64,
    }

    @(Instruction.nop) static struct Nop { string comment; }
    @(Instruction.call) static struct Call { ushort argCount; FuncDeclaration func; }
    @(Instruction.ret) static struct Return {}

    @(Instruction.copy_frel) static struct CopyFrameRelative { ptrdiff_t stackIndex; }

    @(Instruction.local_store) static struct LocalStore { size_t localSlotIndex; }
    @(Instruction.local_load) static struct LocalLoad { size_t localSlotIndex; }
    @(Instruction.local_store_ind) static struct LocalStoreIndirect { size_t localSlotIndex; }
    @(Instruction.local_load_ind) static struct LocalLoadIndirect { size_t localSlotIndex; }

    @(Instruction.ld_i8Bool) static struct LoadI8Bool{ bool arg; }
    @(Instruction.ld_i8) static struct LoadI8{ byte arg; }
    @(Instruction.ld_i16) static struct LoadI16{ short arg; }
    @(Instruction.ld_i32) static struct LoadI32{ int arg; }
    @(Instruction.ld_i64) static struct LoadI64{ long arg; }
    @(Instruction.ld_u8) static struct LoadU8{ ubyte arg; }
    @(Instruction.ld_u16) static struct LoadU16{ ushort arg; }
    @(Instruction.ld_u32) static struct LoadU32{ uint arg; }
    @(Instruction.ld_u64) static struct LoadU64{ ulong arg; }
    @(Instruction.ld_func_ctx) static struct LoadFuncContext{ }

    @(Instruction.cvt_i8_16) static struct ConvertI8To16{ }
    @(Instruction.cvt_i8_32) static struct ConvertI8To32{ }
    @(Instruction.cvt_i8_64) static struct ConvertI8To64{ }
    @(Instruction.cvt_i16_8) static struct ConvertI16To8{ }
    @(Instruction.cvt_i16_32) static struct ConvertI16To32{ }
    @(Instruction.cvt_i16_64) static struct ConvertI16To64{ }
    @(Instruction.cvt_i32_8) static struct ConvertI32To8{ }
    @(Instruction.cvt_i32_16) static struct ConvertI32To16{ }
    @(Instruction.cvt_i32_64) static struct ConvertI32To64{ }
    @(Instruction.cvt_i64_8) static struct ConvertI64To8{ }
    @(Instruction.cvt_i64_16) static struct ConvertI64To16{ }
    @(Instruction.cvt_i64_32) static struct ConvertI64To32{ }

    @(Instruction.cvt_u8_16) static struct ConvertU8To16{ }
    @(Instruction.cvt_u8_32) static struct ConvertU8To32{ }
    @(Instruction.cvt_u8_64) static struct ConvertU8To64{ }
    @(Instruction.cvt_u16_8) static struct ConvertU16To8{ }
    @(Instruction.cvt_u16_32) static struct ConvertU16To32{ }
    @(Instruction.cvt_u16_64) static struct ConvertU16To64{ }
    @(Instruction.cvt_u32_8) static struct ConvertU32To8{ }
    @(Instruction.cvt_u32_16) static struct ConvertU32To16{ }
    @(Instruction.cvt_u32_64) static struct ConvertU32To64{ }
    @(Instruction.cvt_u64_8) static struct ConvertU64To8{ }
    @(Instruction.cvt_u64_16) static struct ConvertU64To16{ }
    @(Instruction.cvt_u64_32) static struct ConvertU64To32{ }

    @(Instruction.cvt_u_i) static struct ConvertUToI{ }
    @(Instruction.cvt_i_u) static struct ConvertIToU{ }

    @(Instruction.add_i8) static struct AddI8{ }
    @(Instruction.add_i16) static struct AddI16{ }
    @(Instruction.add_i32) static struct AddI32{ }
    @(Instruction.add_i64) static struct AddI64{ }
    @(Instruction.add_u8) static struct AddU8{ }
    @(Instruction.add_u16) static struct AddU16{ }
    @(Instruction.add_u32) static struct AddU32{ }
    @(Instruction.add_u64) static struct AddU64{ }

    @(Instruction.div_i8) static struct DivI8{ }
    @(Instruction.div_i16) static struct DivI16{ }
    @(Instruction.div_i32) static struct DivI32{ }
    @(Instruction.div_i64) static struct DivI64{ }
    @(Instruction.div_u8) static struct DivU8{ }
    @(Instruction.div_u16) static struct DivU16{ }
    @(Instruction.div_u32) static struct DivU32{ }
    @(Instruction.div_u64) static struct DivU64{ }

    @(Instruction.mul_i8) static struct MulI8{ }
    @(Instruction.mul_i16) static struct MulI16{ }
    @(Instruction.mul_i32) static struct MulI32{ }
    @(Instruction.mul_i64) static struct MulI64{ }
    @(Instruction.mul_u8) static struct MulU8{ }
    @(Instruction.mul_u16) static struct MulU16{ }
    @(Instruction.mul_u32) static struct MulU32{ }
    @(Instruction.mul_u64) static struct MulU64{ }

    @(Instruction.sub_i8) static struct SubI8{ }
    @(Instruction.sub_i16) static struct SubI16{ }
    @(Instruction.sub_i32) static struct SubI32{ }
    @(Instruction.sub_i64) static struct SubI64{ }
    @(Instruction.sub_u8) static struct SubU8{ }
    @(Instruction.sub_u16) static struct SubU16{ }
    @(Instruction.sub_u32) static struct SubU32{ }
    @(Instruction.sub_u64) static struct SubU64{ }

    static union Data
    {
        static foreach(memberName; __traits(allMembers, CTFEOpcode))
            static if(is(__traits(getMember, CTFEOpcode, memberName) == struct))
                mixin(
                    memberName
                    ~ " "
                    ~ __traits(
                        identifier,
                        __traits(
                            getAttributes,
                            __traits(
                                getMember,
                                CTFEOpcode,
                                memberName
                            )
                        )[0])
                    ~ ";");
    }
    Data data;
    Instruction instruction;

    this(DataT)(DataT data)
    {
        static foreach(memberName; __traits(allMembers, Data))
        {{
            alias Member = __traits(getMember, Data, memberName);
            alias MemberT = typeof(Member);
            static if(is(MemberT == DataT))
            {
                mixin("this.data."~memberName~" = data;");
                this.instruction = mixin("Instruction."~memberName);
            }
        }}
    }
}

private struct CTFEValue
{
    private alias GetT(string TypeName) = __traits(getAttributes, __traits(getMember, Type, TypeName))[0];
    private alias T(TT) = TT;

    static struct StartOfStackFrame {}

    static struct FuncContext 
    {
        size_t localStartIndex;
    }

    static struct LocalSlotReference
    {
        size_t localSlot;
    }

    private static enum Type
    {
        @T!bool i8Bool,
        @T!byte i8,
        @T!short i16,
        @T!int i32,
        @T!long i64,
        @T!ubyte u8,
        @T!ushort u16,
        @T!uint u32,
        @T!ulong u64,
        @T!FuncDeclaration funcPointer,
        @T!StartOfStackFrame startOfFrame,
        @T!FuncContext funcContext,
        @T!LocalSlotReference localSlotRef,

        @T!Dsymbol typePtr, // Special type used for the `alloc` opcode
    }

    private static union Union
    {
        static foreach(memberName; __traits(allMembers, Type))
            mixin("GetT!memberName "~memberName~";");
    }
    
    Type type;
    Union value;

    this(ValueT)(ValueT value)
    {
        static foreach(memberName; __traits(allMembers, Type))
        static if(is(ValueT == GetT!memberName))
        {
            mixin("this.value."~memberName~" = value;");
            this.type = mixin("Type."~memberName);
            return;
        }

        assert(false, "This shouldn't happen");
    }

    OutT asPtr(OutT)()
    {
        static foreach(memberName; __traits(allMembers, Type))
        static if(is(OutT == GetT!memberName*))
        {
            import std;
            assert(this.type == mixin("Type."~memberName), format("I'm a %s but we wanted a %s", this.type, memberName));
            return mixin("&this.value."~memberName);
        }

        assert(false, "This shouldn't happen");
    }

    string toString() const
    {
        import std.conv : to;
        import std.format : format;
        switch(this.type) with(Type)
        {
            static foreach(typeName; __traits(allMembers, Type))
            {
                case mixin(typeName):
                    return mixin(`"(`~typeName~`)%s".format(this.value.`~typeName~`)`);
            }

            default:
                return "(UNKNOWN:"~this.type.to!string~")";
        }
    }
}

private struct CTFEVirtualMachine
{
    Array!CTFEOpcode _opcodes;
    Array!CTFEValue  _stack;
    Array!CTFEValue  _locals;

    void addLocalCapacity(size_t amount)
    {
        this._locals.setDim(this._locals.length + amount);
    }

    void shrinkLocalCapacity(size_t amount)
    {
        this._locals.setDim(this._locals.length - amount);
    }

    void setLocal(size_t index, CTFEValue value)
    {
        this._locals[index] = value;
    }

    CTFEValue getLocal(size_t index)
    {
        return this._locals[index];
    }

    size_t getLocalSlotIndex()
    {
        return this._locals.length;
    }

    void appendOpcode(Opcode)(Opcode opcode)
    {
        this._opcodes.push(CTFEOpcode(opcode));
    }

    size_t getOpcodeIndex()
    {
        return this._opcodes.length;
    }

    void push(CTFEValue value)
    {
        this._stack.push(value);
    }

    void reserve(size_t amount)
    {
        this._stack.setDim(this._stack.length + amount);
    }

    CTFEValue pop()
    {
        return this._stack.pop();
    }

    CTFEValue popFollowRef()
    {
        auto value = this.pop();
        if(value.type == CTFEValue.Type.localSlotRef)
            return this._locals[value.value.localSlotRef.localSlot];
        else
            return value;
    }

    CTFEValue[Amount] popMany(size_t Amount)()
    {
        CTFEValue[Amount] values;

        foreach(i; 0..Amount)
            values[i] = this._stack.pop();

        return values;
    }

    CTFEValue get(ptrdiff_t index)
    {
        return this._stack[index];
    }

    size_t getStackIndex()
    {
        return this._stack.length;
    }

    size_t getIndexOfStackFrameStart()
    {
        for(size_t i = this._stack.length; i > 1; i--)
        {
            if(this.get(i-1).type == CTFEValue.Type.startOfFrame)
                return i;
        }

        assert(false);
    }

    void call(scope FuncDeclaration func, scope CTFEValue[] args, scope out CTFEValue ret)
    {
        if(!func.ctfeInfo.hasBeenGenerated)
            compileFunction(func, this);
        assert(func.ctfeInfo.hasBeenGenerated, "Function was not compiled?");

        const stackLength = this._stack.length;
        const localsLength = this._locals.length;

        this.push(CTFEValue(CTFEValue.StartOfStackFrame()));
        for(long i = cast(long)args.length-1; i >= 0; i--)
            this.push(args[i]);
        executeFunction(func.ctfeInfo, ret, this);

        assert(this.pop().type == CTFEValue.Type.startOfFrame);
        assert(this._stack.length == stackLength);
        assert(this._locals.length == localsLength);
    }

    void _debug()
    {
        import std;

        auto f = File("/Users/bradleychatha/Desktop/Coding/dmd/vm.txt", "wb");

        foreach(opcode; this._opcodes)
        {
            Switch: final switch(opcode.instruction) with(CTFEOpcode.Instruction)
            {
                static foreach(instName; __traits(allMembers, CTFEOpcode.Instruction))
                {
                    case mixin(instName):
                        auto data = mixin("opcode.data."~instName);
                        f.write(instName);
                        f.write(" ");
                        
                        auto dataTuple = data.tupleof;
                        static foreach(i; 0..dataTuple.length)
                        {{
                            alias DataT = typeof(dataTuple[0]);
                            f.write(dataTuple[i].to!string);

                            static if(i+1 != dataTuple.length)
                                f.write(", ");
                        }}
                        
                        f.write("\n");
                        break Switch;
                }
            }
        }
    }
}
private __gshared CTFEVirtualMachine g_ctfeVirtualMachine;

private:

private extern (C++) final class OpcodeCompiler : Visitor
{
    alias visit = Visitor.visit;
    CTFEVirtualMachine* _vm;
    CTFEFunctionInfo* _funcInfo;
    FuncDeclaration _funcDecl; // May be null

    extern(D) this(CTFEVirtualMachine* vm, CTFEFunctionInfo* funcInfo, FuncDeclaration funcDecl) @nogc nothrow
    {
        this._vm = vm;
        this._funcInfo = funcInfo;
        this._funcDecl = funcDecl;
    }

    static struct BinaryArithPermutation(alias TypeT, alias OpcodeT)
    {
        alias Type   = TypeT;
        alias Opcode = OpcodeT;
    }

    mixin template BinaryArithVisit(alias AstNodeT, Permutations...)
    {
        override void visit(AstNodeT exp)
        {
            import std;
            writeln("    :: ", __traits(identifier, AstNodeT));
            writeln("        e1: ", exp.e1.type, " = ", exp.e1);
            writeln("        e2: ", exp.e2.type, " = ", exp.e2);

            this.visit(exp.e2);
            this.visit(exp.e1);
            if(this.hadErrors())
            {
                exp.error("[CTFE] Unable to compile _ - Compilation of sub expression(s) failed");
                return;
            }

            static foreach(permutation; Permutations)
            {
                if(exp.type == permutation.Type)
                {
                    this._vm.appendOpcode(permutation.Opcode());
                    return;
                }
            }

            exp.error("[CTFE] Unable to compile _ - Unhandled target type");
        }
    }

public:

    bool hadErrors()
    {
        return false;
    }

    override void visit(Statement statement)
    {
        import std;
        writeln(":: Statement");
        writeln("    stmt: STMT.", statement.stmt, " = ", statement);

        if(auto compound = statement.isCompoundStatement())
        {
            foreach(s; *compound.statements)
                this.visit(s);
            return;
        }
        else if(auto v = statement.isReturnStatement())
        {
            this.visit(v);
            return;
        }
        else if(auto v = statement.isExpStatement())
        {
            this.visit(v.exp);
            return;
        }

        statement.error("statement `%s` cannot be interpreted at compile time", statement.toChars());
    }

    override void visit(ReturnStatement statement)
    {
        import std;
        writeln(":: ReturnStatement");
        writeln("    exp: ", statement.exp);
        writeln("    caseDim: ", statement.caseDim);

        this.visit(statement.exp);
        this._vm.appendOpcode(CTFEOpcode.Return());
    }

    mixin BinaryArithVisit!(AddExp,
        BinaryArithPermutation!(Type.tint8, CTFEOpcode.AddI8),
        BinaryArithPermutation!(Type.tint16, CTFEOpcode.AddI16),
        BinaryArithPermutation!(Type.tint32, CTFEOpcode.AddI32),
        BinaryArithPermutation!(Type.tint64, CTFEOpcode.AddI64),
        BinaryArithPermutation!(Type.tuns8, CTFEOpcode.AddU8),
        BinaryArithPermutation!(Type.tuns16, CTFEOpcode.AddU16),
        BinaryArithPermutation!(Type.tuns32, CTFEOpcode.AddU32),
        BinaryArithPermutation!(Type.tuns64, CTFEOpcode.AddU64),
    ) VisitAddExp;

    mixin BinaryArithVisit!(DivExp,
        BinaryArithPermutation!(Type.tint8, CTFEOpcode.DivI8),
        BinaryArithPermutation!(Type.tint16, CTFEOpcode.DivI16),
        BinaryArithPermutation!(Type.tint32, CTFEOpcode.DivI32),
        BinaryArithPermutation!(Type.tint64, CTFEOpcode.DivI64),
        BinaryArithPermutation!(Type.tuns8, CTFEOpcode.DivU8),
        BinaryArithPermutation!(Type.tuns16, CTFEOpcode.DivU16),
        BinaryArithPermutation!(Type.tuns32, CTFEOpcode.DivU32),
        BinaryArithPermutation!(Type.tuns64, CTFEOpcode.DivU64),
    ) VisitDivExp;

    mixin BinaryArithVisit!(MulExp,
        BinaryArithPermutation!(Type.tint8, CTFEOpcode.MulI8),
        BinaryArithPermutation!(Type.tint16, CTFEOpcode.MulI16),
        BinaryArithPermutation!(Type.tint32, CTFEOpcode.MulI32),
        BinaryArithPermutation!(Type.tint64, CTFEOpcode.MulI64),
        BinaryArithPermutation!(Type.tuns8, CTFEOpcode.MulU8),
        BinaryArithPermutation!(Type.tuns16, CTFEOpcode.MulU16),
        BinaryArithPermutation!(Type.tuns32, CTFEOpcode.MulU32),
        BinaryArithPermutation!(Type.tuns64, CTFEOpcode.MulU64),
    ) VisitMulExp;

    mixin BinaryArithVisit!(MinExp,
        BinaryArithPermutation!(Type.tint8, CTFEOpcode.SubI8),
        BinaryArithPermutation!(Type.tint16, CTFEOpcode.SubI16),
        BinaryArithPermutation!(Type.tint32, CTFEOpcode.SubI32),
        BinaryArithPermutation!(Type.tint64, CTFEOpcode.SubI64),
        BinaryArithPermutation!(Type.tuns8, CTFEOpcode.SubU8),
        BinaryArithPermutation!(Type.tuns16, CTFEOpcode.SubU16),
        BinaryArithPermutation!(Type.tuns32, CTFEOpcode.SubU32),
        BinaryArithPermutation!(Type.tuns64, CTFEOpcode.SubU64),
    ) VisitMinExp;

    override void visit(Expression exp)
    {
        import std;
        writeln(":: Expression");
        writeln("    exp: EXP.", exp.op, " = ", exp);
        writeln("    type: ", exp.type);

        if(auto v = exp.isIntegerExp())
        {
            this.visit(v);
            return;
        }
        else if(auto v = exp.isCastExp())
        {
            this.visit(v);
            return;
        }
        else if(auto v = exp.isAddExp())
        {
            VisitAddExp.visit(v);
            return;
        }
        else if(auto v = exp.isDivExp())
        {
            VisitDivExp.visit(v);
            return;
        }
        else if(auto v = exp.isMulExp())
        {
            VisitMulExp.visit(v);
            return;
        }
        else if(auto v = exp.isMinExp())
        {
            VisitMinExp.visit(v);
            return;
        }
        else if(auto v = exp.isCallExp())
        {
            this.visit(v);
            return;
        }
        else if(auto v = exp.isDeclarationExp())
        {
            this.visit(v);
            return;
        }
        else if(auto v = exp.isConstructExp())
        {
            this.visit(v);
            return;
        }
        else if(auto v = exp.isVarExp())
        {
            this.visit(v);
            return;
        }
        else if(auto v = exp.isBlitExp())
        {
            this.visit(v);
            return;
        }
        else if(auto v = exp.isAssignExp())
        {
            this.visit(v);
            return;
        }

        exp.error("[CTFE2] Unable to compile Expression - unhandled expression type");
    }

    override void visit(IntegerExp exp)
    {
        import std;
        writeln("    :: IntegerExp");
        switch(exp.op)
        {
            case EXP.int64:
                if(exp.type == Type.tint8) 
                    this._vm.appendOpcode(CTFEOpcode.LoadI8(cast(byte)exp.toInteger())); 
                else if(exp.type == Type.tint16) 
                    this._vm.appendOpcode(CTFEOpcode.LoadI16(cast(short)exp.toInteger())); 
                else if(exp.type == Type.tint32) 
                    this._vm.appendOpcode(CTFEOpcode.LoadI32(cast(int)exp.toInteger())); 
                else if(exp.type == Type.tint64) 
                    this._vm.appendOpcode(CTFEOpcode.LoadI64(cast(long)exp.toInteger())); 
                else if(exp.type == Type.tbool)
                    this._vm.appendOpcode(CTFEOpcode.LoadI8Bool(exp.toInteger() != 0));
                else if(exp.type == Type.tuns8) 
                    this._vm.appendOpcode(CTFEOpcode.LoadU8(cast(ubyte)exp.toInteger())); 
                else if(exp.type == Type.tuns16) 
                    this._vm.appendOpcode(CTFEOpcode.LoadU16(cast(ushort)exp.toInteger())); 
                else if(exp.type == Type.tuns32) 
                    this._vm.appendOpcode(CTFEOpcode.LoadU32(cast(uint)exp.toInteger())); 
                else if(exp.type == Type.tuns64) 
                    this._vm.appendOpcode(CTFEOpcode.LoadU64(cast(ulong)exp.toInteger())); 
                else
                    exp.error("[CTFE2] Unable to compile IntegerExp - unhandled native integer type");
                break;
            default:
                exp.error("[CTFE2] Unable to compile IntegerExp - unhandled integer expression type");
                break;
        }
    }

    override void visit(CastExp exp)
    {
        import std;
        writeln("    :: CastExp");
        writeln("        to: ", exp.to);
        writeln("        e1: ", exp.e1);

        this.visit(exp.e1);

        if(exp.to.isintegral())
        {
            this.emitNumericCast(exp);
            return;
        }

        exp.error("[CTFE] Unable to compile CastExp - Unhandled target type");
    }

    override void visit(CallExp exp)
    {
        import std;
        writeln("    :: CallExp");
        writeln("        e1: ", exp.e1);
        writeln("        func: ", exp.f);
        writeln("        args: ", exp.arguments.length);
        writeln("        direct: ", exp.directcall);

        for(long i = (cast(long)exp.arguments.length) - 1; i >= 0; i--)
            this.visit(exp.arguments.opIndex(i));

        // If we're calling a nested function; then we need to pass in all the relevant frame pointers
        const frameCount = getNestedFrameCount(exp.f);
        if(frameCount > 0)
        {
            const parentFrameCounts = frameCount - 1;

            // Push our parent frames.
            for(ptrdiff_t i = parentFrameCounts - 1; i >= 0; i--) // - 1 to make things 0-based.
            {
                auto symbol = this._funcInfo.getAnonymousSymbolForContextPointer(i);
                const slot = this._funcInfo.getLocalSlotIndex(symbol);
                this._vm.appendOpcode(CTFEOpcode.LocalLoad(i));
            }

            // Push our own frame.
            this._vm.appendOpcode(CTFEOpcode.LoadFuncContext());
        }

        const argCount = cast(ushort)(exp.arguments.length + frameCount);
        assert(argCount <= ushort.max);
        this._vm.appendOpcode(CTFEOpcode.Call(argCount, exp.f));
    }

    override void visit(DeclarationExp exp)
    {
        import std;
        writeln("    :: DeclarationExp");
        writeln("        decl: ", exp.declaration);

        if(auto v = exp.declaration.isVarDeclaration())
        {
            this.emitVarDeclaration(v);
            return;
        }

        exp.error("[CTFE] Unable to compile DeclarationExp - Unsupported: ", exp.toChars());
    }

    override void visit(ConstructExp exp)
    {
        import std;
        writeln("    :: ConstructExp");
        writeln("        e1: ", exp.e1);
        writeln("        e2: ", exp.e2);

        this.visit(exp.e2);
        this.emitStore(exp.e1);
    }

    override void visit(BlitExp exp)
    {
        import std;
        writeln("    :: BlitExp");
        writeln("        e1: ", exp.e1);
        writeln("        e2: ", exp.e2);

        this.visit(exp.e2);
        this.emitStore(exp.e1, true);
    }

    override void visit(AssignExp exp)
    {
        import std;
        writeln("    :: AssignExp");
        writeln("        e1: ", exp.e1);
        writeln("        e2: ", exp.e2);

        this.visit(exp.e2);
        this.emitStore(exp.e1, true);
    }

    // This is only for LOADING a VarExp; storing is handled specially by `emitStore`
    override void visit(VarExp exp)
    {
        import std;
        writeln("    :: VarExp");
        writeln("        var: ", exp.var);

        const frameCount = !!this._funcDecl ? getNestedFrameCount(this._funcDecl) : 0;

        if(frameCount == 0)
        {
            const slot = this._funcInfo.getLocalSlotIndex(exp.var);
            this._vm.appendOpcode(CTFEOpcode.LocalLoad(slot));
        }
        else
        {
            auto f = this._funcDecl;
            this.emitPossibleIndirectLoad(f, exp.var);
        }
    }

private:

    void emitNumericCast(CastExp exp)
    {
        const toSign = this.isSigned(exp.to);
        const fromSign = this.isSigned(exp.e1.type);

        if(toSign && !fromSign)
            this._vm.appendOpcode(CTFEOpcode.ConvertUToI());
        else if(!toSign && fromSign)
            this._vm.appendOpcode(CTFEOpcode.ConvertIToU());
        
        exp.error("[CTFE] Unable to compile CastExp - Unhandled numeric cast");
    }

    bool isSigned(Type t)
    {
        return t == Type.tint8 || t == Type.tint16 || t == Type.tint32 || t == Type.tint64;
    }

    void emitStore(Expression exp, bool isBlit = false)
    {
        import std;
        writeln(":: emitStore");
        writeln("    exp: ", exp);
        writeln("    blit: ", isBlit);

        if(auto v = exp.isVarExp())
        {
            writeln("    :: VarExp");
            writeln("        var: ", v.var);

            const frameCount = !!this._funcDecl ? getNestedFrameCount(this._funcDecl) : 0;
            if(frameCount == 0)
            {
                const slot = this._funcInfo.getLocalSlotIndex(v.var);
                this._vm.appendOpcode(CTFEOpcode.LocalStore(slot));
            }
            else
            {
                auto f = this._funcDecl;
                this.emitPossibleIndirectStore(f, v.var);
            }
            return;
        }

        exp.error("[CTFE2] Unable to compile STORE Expression - unhandled");
    }

    void emitVarDeclaration(VarDeclaration decl)
    {
        import std;
        writeln("        :: VarDeclaration");
        writeln("            type: ", decl.type);
        writeln("            ident: ", decl.ident);
        writeln("            parent: ", decl.parent);
        writeln("            static: ", decl.isStatic);
        writeln("            ctfe: ", decl.isCTFE);
        writeln("            init: ", decl._init);
        writeln("            sc: ", decl.storage_class);
        writeln("            vis: ", decl.visibility);
        writeln("            inuse: ", decl.inuse);
        writeln("            alias: ", decl.aliassym);
        writeln("            edtor: ", decl.edtor);
        writeln("            range: ", decl.range);
        writeln("            maybes: ", decl.maybes);
        writeln("            offset: ", decl.offset);
        writeln("            seq: ", decl.sequenceNumber);
        writeln("            align: ", decl.alignment);
        writeln("            assign: ", decl.canassign);

        if(cast(int)decl.storage_class == 134217728)
            return;

        switch(decl._init.kind)
        {
            case InitKind.exp:
                auto expDecl = cast(ExpInitializer)decl._init;
                this.visit(expDecl.exp);
                return;

            default:
                break;
        }

        decl.error("[CTFE] Unable to compile VarDeclaration - Unsupported");
    }

    alias emitPossibleIndirectLoad = emitPossibleIndirect!(CTFEOpcode.LocalLoad, CTFEOpcode.LocalLoadIndirect);
    alias emitPossibleIndirectStore = emitPossibleIndirect!(CTFEOpcode.LocalStore, CTFEOpcode.LocalStoreIndirect);
    void emitPossibleIndirect(DirectT, IndirectT)(scope FuncDeclaration f, scope Declaration var)
    {
        size_t frameIndex;
        while(f)
        {
            scope(exit) frameIndex++;

            scope ptr = f.ctfeInfo.tryGetLocalSlotIndex(var);
            if(ptr)
            {
                if(f is this._funcDecl)
                    this._vm.appendOpcode(DirectT(*ptr));
                else
                {
                    auto symbol = this._funcInfo.getAnonymousSymbolForContextPointer(frameIndex-1); // -1 since we start at 0
                    const slot = this._funcInfo.tryGetLocalSlotIndex(symbol);
                    assert(slot);
                    this._vm.appendOpcode(CTFEOpcode.LocalLoad(*slot));
                    this._vm.appendOpcode(IndirectT(*ptr));
                }
                break;
            }

            if(f.toParent2())
                f = f.toParent2().isFuncDeclaration();
            else
                f = null;
        }
    }
}

// BOOKMARK: Misc Helper Functions
size_t getNestedFrameCount(scope FuncDeclaration func)
{
    size_t count;
    auto falias = func.toAliasFunc();
    while(falias && falias.toParent2())
    {
        if(auto f = falias.toParent2().isFuncDeclaration())
        {
            falias = f.toAliasFunc();
            count++;
        }
        else
            break;
    }

    return count;
}

// BOOKMARK: Opcode Compilation
bool compileFunction(scope FuncDeclaration func, scope ref CTFEVirtualMachine vm)
{
    import std;
    writeln(":: compileFunction");
    writeln("    func: ", func);
    writeln("    run: ", func.semanticRun);

    func.ctfeInfo.opcodeStartIndex = vm.getOpcodeIndex();
    vm.appendOpcode(CTFEOpcode.Nop("START FUNCTION - %s".format(func)));

    // Add code to handle function context parameters
    const contextCount = getNestedFrameCount(func);
    foreach(i; 0..contextCount)
    {
        auto symbol = func.ctfeInfo.getAnonymousSymbolForContextPointer(i);
        const slot = func.ctfeInfo.getLocalSlotIndex(symbol);
        vm.appendOpcode(CTFEOpcode.LocalStore(slot));
    }

    // Add code to handle parameters
    if(func.parameters)
    foreach(arg; *func.parameters)
    {
        const slot = func.ctfeInfo.getLocalSlotIndex(arg);
        vm.appendOpcode(CTFEOpcode.LocalStore(slot));
    }

    // Compile body
    scope OpcodeCompiler compiler = new OpcodeCompiler(&vm, &func.ctfeInfo, func);
    compiler.visit(func.fbody);
    if(compiler.hadErrors)
    {
        writeln("!! compileFunction");
        return false;
    }

    vm.appendOpcode(CTFEOpcode.Nop("END FUNCTION - %s".format(func)));
    func.ctfeInfo.opcodeEndIndex = vm.getOpcodeIndex();
    writeln("^^ compileFunction");
    writeln("    info: ", func.ctfeInfo);
    writeln("    opcodes: ", vm._opcodes[func.ctfeInfo.opcodeStartIndex..func.ctfeInfo.opcodeEndIndex]);

    vm._debug();
    return true;
}

bool compileExpressionAsFunction(scope Expression exp, scope ref CTFEVirtualMachine vm, scope ref CTFEFunctionInfo info)
{
    import std;
    writeln(":: compileExpressionAsFunction");
    writeln("    exp: ", exp);

    info.opcodeStartIndex = vm.getOpcodeIndex();
    vm.appendOpcode(CTFEOpcode.Nop("START EXPRESSION AS FUNCTION - %s".format(exp)));

    scope OpcodeCompiler compiler = new OpcodeCompiler(&vm, &info, null);
    compiler.visit(exp);
    if(compiler.hadErrors)
    {
        writeln("!! compileExpressionAsFunction");
        return false;
    }
    vm.appendOpcode(CTFEOpcode.Return());

    vm.appendOpcode(CTFEOpcode.Nop("END EXPRESSION AS FUNCTION - %s".format(exp)));
    info.opcodeEndIndex = vm.getOpcodeIndex();
    writeln("^^ compileExpressionAsFunction");
    writeln("    info: ", info);
    writeln("    opcodes: ", vm._opcodes[info.opcodeStartIndex..info.opcodeEndIndex]);
    return true;
}

// BOOKMARK: Opcode execution
template InstructionPopCount(string instructionName)
{
    alias Instruction = __traits(getMember, CTFEOpcode.Instruction, instructionName);

    alias UDAs = __traits(getAttributes, Instruction);
    static assert(is(typeof(UDAs[0]) == Pops));

    enum InstructionPopCount = UDAs[0].amount;
}

template InstructionPushCount(string instructionName)
{
    alias Instruction = __traits(getMember, CTFEOpcode.Instruction, instructionName);

    alias UDAs = __traits(getAttributes, Instruction);
    static assert(is(typeof(UDAs[1]) == Pushes));

    enum InstructionPushCount = UDAs[1].amount;
}

void executeFunction(scope CTFEFunctionInfo info, scope out CTFEValue retVal, scope ref CTFEVirtualMachine vm)
{
    const localStartIndex = vm.getLocalSlotIndex();
    vm.addLocalCapacity(info.localSlotIndexMap.length);
    scope(exit) vm.shrinkLocalCapacity(info.localSlotIndexMap.length);

    vm._locals[localStartIndex..$][] = CTFEValue.init;

    Foreach: foreach(i; info.opcodeStartIndex..info.opcodeEndIndex)
    {
        CTFEOpcode op = vm._opcodes[i];
        import std;
        writeln("EXECUTE: ", op);
        writeln("(before) LOCALS: ", vm._locals[localStartIndex..$]);
        writeln("(before) STACK: ", vm._stack[0..$]);
        Switch: final switch(op.instruction) with(CTFEOpcode.Instruction)
        {
            case call:
                _opcode_call(op.data.call, info, vm);
                break;

            case ret:
                _opcode_ret(op.data.ret, retVal, vm);
                break Foreach;

            case local_store:
                _opcode_local_store(op.data.local_store, localStartIndex, vm);
                break;

            case local_load:
                _opcode_local_load(op.data.local_load, localStartIndex, vm);
                break;

            case local_store_ind:
                _opcode_local_store_ind(op.data.local_store, vm);
                break;

            case local_load_ind:
                _opcode_local_load_ind(op.data.local_load, vm);
                break;

            case ld_func_ctx:
                _opcode_ld_func_ctx(op.data.ld_func_ctx, localStartIndex, vm);
                break;

            static foreach(memberName; __traits(allMembers, CTFEOpcode.Instruction))
            {
                static if(memberName != "call" 
                && memberName != "ret" 
                && memberName != "local_load" 
                && memberName != "local_store"
                && memberName != "local_store_ind"
                && memberName != "local_load_ind"
                && memberName != "ld_func_ctx")
                {
                    case mixin(memberName):
                        alias FuncName = InstructionFuncName!(__traits(getMember, CTFEOpcode.Instruction, memberName));
                        alias Func = __traits(getMember, dmd.ctfejit, FuncName);
                        Func(vm, op);
                        break Switch;
                }
            }
        }
        writeln("(after) LOCALS: ", vm._locals[localStartIndex..$]);
        writeln("(after) STACK: ", vm._stack[0..$]);
        writeln("--------------------------");
    }
}

// BOOKMARK: Helper Templates
template InstructionFromDataType(alias InstructionDataType)
{
    alias InstructionFromDataType = __traits(getAttributes, InstructionDataType)[0];
}

template DataTypeFromInstruction(alias Instruction)
{
    static foreach(memberName; __traits(allMembers, CTFEOpcode))
    static if(is(
        __traits(getAttributes, __traits(getMember, CTFEOpcode, memberName))
        ==
        Instruction
    ))
    {
        alias DataTypeFromInstruction = __traits(getMember, CTFEOpcode, memberName);
    }
}

template InstructionFuncName(alias Instruction)
{
    immutable InstructionFuncName = "ctfe_"~__traits(identifier, Instruction);
}

template InstructionUda(alias Instruction, alias UDAT)
{
    static foreach(attrib; __traits(getAttributes, Instruction))
    {
        static if(__traits(compiles, isInstanceOf!(UDAT, typeof(attrib))))
        {
            static if(isInstanceOf!(UDAT, typeof(attrib)))
                alias InstructionUda = attrib;
        }
        else
        {
            static if(isInstanceOf!(UDAT, attrib))
                alias InstructionUda = attrib;
        }
    }

    static if(!__traits(compiles, InstructionUda.init))
        alias InstructionUda = void;
}

template InstructionHasUda(alias Instruction, alias UDAT)
{
    enum InstructionHasUda = !is(InstructionUda!(Instruction, UDAT) == void);
}

// TODO: Figure out where to put this or what to replace it with.
/**
 * Returns true if T is an instance of the template S.
 */
enum bool isInstanceOf(alias S, T) = is(T == S!Args, Args...);
/// ditto
template isInstanceOf(alias S, alias T)
{
    enum impl(alias T : S!Args, Args...) = true;
    enum impl(alias T) = false;
    enum isInstanceOf = impl!T;
}

// BOOKMARK: Generation Templates

mixin template OpcodeHandler(string memberName)
{
    alias Handler = __traits(getMember, dmd.ctfejit, memberName);
    alias Instruction = __traits(getAttributes, Handler)[0];
    enum InstructionAsValue = mixin("CTFEOpcode.Instruction."~__traits(identifier, Instruction));

    alias UDAs = __traits(getAttributes, Instruction);
    static assert(is(typeof(UDAs[0]) == Pops));
    static assert(is(typeof(UDAs[1]) == Pushes));

    enum PopCount  = UDAs[0].amount;
    enum PushCount = UDAs[1].amount;

    static assert(!UDAs[0].dynamic, "Instructions with a dynamic pop count must be specially handled.");
    static assert(!UDAs[1].dynamic, "Instructions with a dynamic push count must be specially handled.");

    static if (is(typeof(Handler) P == function))
        alias HandlerParameters = P;
    else static assert(false, "Can't extract parameters for function");

    mixin("@(Instruction) void "~InstructionFuncName!Instruction~"(scope ref CTFEVirtualMachine vm, CTFEOpcode opcode)
    {
        assert(opcode.instruction == InstructionAsValue);

        HandlerParameters params;
        CTFEValue[PushCount] outputs;
        
        static if(is(HandlerParameters[0] == CTFEVirtualMachine*))
        {
            params[0] = &vm;
            params[1] = opcode.data."~__traits(identifier, Instruction)~";
            enum StaticArgs = 2;
        }
        else
        {
            params[0] = opcode.data."~__traits(identifier, Instruction)~";
            enum StaticArgs = 1;
        }

        static foreach(i; 0..PopCount)
        {
            static if(is(HandlerParameters[StaticArgs+i] == CTFEValue))
                params[StaticArgs+i] = vm.pop();
            else
            {
                params[StaticArgs+i] = *vm.popFollowRef().asPtr!(HandlerParameters[StaticArgs+i]*);
            }
        }
        static foreach(i; 0..PushCount)
        {
            static if(is(HandlerParameters[StaticArgs+i+PopCount] == CTFEValue*))
            {
                outputs[i] = CTFEValue.init;
                params[StaticArgs+i+PopCount] = &outputs[i];
            }
            else
            {
                outputs[i] = CTFEValue(typeof(*HandlerParameters[StaticArgs+i+PopCount]).init);
                params[StaticArgs+i+PopCount] = outputs[i].asPtr!(HandlerParameters[StaticArgs+i+PopCount]);
            }
        }

        Handler(params);

        foreach(output; outputs)
            vm.push(output);
    }");
}

mixin template GenerateBinaryArithmeticHandler(alias InstructionDataType)
{
    alias Instruction    = InstructionFromDataType!InstructionDataType;
    alias BinaryArithUda = InstructionUda!(Instruction, BinaryArith);

    mixin("
        @Instruction void opcode_"~InstructionFuncName!Instruction~"(
            InstructionDataType op,
            BinaryArithUda.Type i1,
            BinaryArithUda.Type i2,
            scope BinaryArithUda.Type* r1,
        )
        {
            *r1 = cast(BinaryArithUda.Type)(i1 "~BinaryArithUda.operation~" i2);
        }
    ");
}

mixin template GenerateLoadHandler(alias InstructionDataType)
{
    alias Instruction = InstructionFromDataType!InstructionDataType;
    alias LoadUda     = InstructionUda!(Instruction, Load);

    mixin("
        @Instruction void opcode_"~InstructionFuncName!Instruction~"(
            InstructionDataType op,
            scope LoadUda.Type* r1,
        )
        {
            *r1 = op.arg;
        }
    ");
}

mixin template GenerateConvertHandler(alias InstructionDataType)
{
    alias Instruction = InstructionFromDataType!InstructionDataType;
    alias ConvertUda  = InstructionUda!(Instruction, Convert);

    mixin("
        @Instruction void opcode_"~InstructionFuncName!Instruction~"(
            InstructionDataType op,
            ConvertUda.From i1,
            scope ConvertUda.To* r1,
        )
        {
            *r1 = cast(ConvertUda.To)i1;
        }
    ");
}

mixin template TryToAutomaticallyGenerateOpcode(string dataTypeName)
{
    alias Symbol = __traits(getMember, CTFEOpcode, dataTypeName);
    
    static if(is(Symbol == struct))
    {
        alias Instruction = InstructionFromDataType!Symbol;
        enum IsDataType   = !is(Instruction == void);

        static if(IsDataType)
        {
            static if(InstructionHasUda!(Instruction, BinaryArith))
                mixin GenerateBinaryArithmeticHandler!Symbol;
            else static if(InstructionHasUda!(Instruction, Load))
                mixin GenerateLoadHandler!Symbol;
            else static if(InstructionHasUda!(Instruction, Convert))
                mixin GenerateConvertHandler!Symbol;
        }
    }
}

// BOOKMARK: Generated Opcode Implementations
static foreach(memberName; __traits(allMembers, CTFEOpcode))
    mixin TryToAutomaticallyGenerateOpcode!memberName;

// BOOKMARK: Handler Generation (KEEP BELOW GENERATED OPCODES - otherwise the static foreach can't see the generated symbols)
static foreach(memberName; __traits(allMembers, dmd.ctfejit))
static if(memberName.length >= 7 && memberName[0..7] == "opcode_")
    mixin OpcodeHandler!memberName;

// BOOKMARK: Manual Opcode Implementation
@(CTFEOpcode.Instruction.nop) 
void opcode_nop(CTFEOpcode.Nop op) {}

@(CTFEOpcode.Instruction.copy_frel) 
void opcode_copy_frel(scope CTFEVirtualMachine* vm, CTFEOpcode.CopyFrameRelative op, scope CTFEValue* r1)
{
    const start = vm.getIndexOfStackFrameStart();
    *r1 = vm.get(start + op.stackIndex);
}

@(CTFEOpcode.Instruction.cvt_u_i) 
void opcode_cvt_u_i(CTFEOpcode.ConvertUToI op, CTFEValue i1, scope CTFEValue* r1)
{
    switch(i1.type) with(CTFEValue.Type)
    {
        case u8:  *r1 = CTFEValue(cast(byte)i1.value.u8); break;
        case u16: *r1 = CTFEValue(cast(short)i1.value.u16); break;
        case u32: *r1 = CTFEValue(cast(int)i1.value.u32); break;
        case u64: *r1 = CTFEValue(cast(long)i1.value.u64); break;
        default: assert(false);
    }
}

@(CTFEOpcode.Instruction.cvt_i_u) 
void opcode_cvt_i_u(CTFEOpcode.ConvertIToU op, CTFEValue i1, scope CTFEValue* r1)
{
    switch(i1.type) with(CTFEValue.Type)
    {
        case i8:  *r1 = CTFEValue(cast(ubyte)i1.value.i8); break;
        case i16: *r1 = CTFEValue(cast(ushort)i1.value.i16); break;
        case i32: *r1 = CTFEValue(cast(uint)i1.value.i32); break;
        case i64: *r1 = CTFEValue(cast(ulong)i1.value.i64); break;
        default: assert(false);
    }
}

// The following opcodes are a bit special in that they manipulate things weirdly; so we
// prefix them with `_` to stop a `ctfe_<opcode_name>` function from
// being generated, and we instead manually call these opcodes from the execute loop.

void _opcode_call(CTFEOpcode.Call op, scope ref CTFEFunctionInfo funcInfo, scope ref CTFEVirtualMachine vm)
{
    CTFEValue[SMALL_ARG_ARRAY_SIZE] smallArgArray;
    Array!CTFEValue largeArgArray;
    CTFEValue[] argSlice;

    if(op.argCount <= smallArgArray.length)
        argSlice = smallArgArray[0..op.argCount];
    else
    {
        largeArgArray.setDim(op.argCount);
        argSlice = largeArgArray[0..op.argCount];
    }

    foreach(i; 0..op.argCount)
        argSlice[i] = vm.pop();

    CTFEValue retValue;
    vm.call(op.func, argSlice, retValue);
    vm.push(retValue);
}

void _opcode_ret(CTFEOpcode.Return op, scope out CTFEValue r1, scope ref CTFEVirtualMachine vm)
{
    r1 = vm.pop();
}

void _opcode_local_load(CTFEOpcode.LocalLoad op, const size_t localStartIndex, scope ref CTFEVirtualMachine vm)
{
    vm.push(CTFEValue(CTFEValue.LocalSlotReference(localStartIndex + op.localSlotIndex)));
}

void _opcode_local_store(CTFEOpcode.LocalStore op, const size_t localStartIndex, scope ref CTFEVirtualMachine vm)
{
    auto value = vm.pop();
    vm.setLocal(localStartIndex + op.localSlotIndex, value);
}

void _opcode_local_load_ind(CTFEOpcode.LocalLoad op, scope ref CTFEVirtualMachine vm)
{
    auto ctx = vm.popFollowRef();
    assert(ctx.type == CTFEValue.Type.funcContext);

    vm.push(CTFEValue(CTFEValue.LocalSlotReference(ctx.value.funcContext.localStartIndex + op.localSlotIndex)));
}

void _opcode_local_store_ind(CTFEOpcode.LocalStore op, scope ref CTFEVirtualMachine vm)
{
    auto ctx = vm.popFollowRef();
    auto value = vm.popFollowRef();
    assert(ctx.type == CTFEValue.Type.funcContext);
    vm.setLocal(ctx.value.funcContext.localStartIndex + op.localSlotIndex, value);
}

void _opcode_ld_func_ctx(CTFEOpcode.LoadFuncContext op, size_t localStartIndex, scope ref CTFEVirtualMachine vm)
{
    vm.push(CTFEValue(CTFEValue.FuncContext(localStartIndex)));
}