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
        case valuePtr:
        case typePtr:
            return CTFEExp.cantexp;
    }
}

// BOOKMARK: Data Structures
private enum SMALL_ARG_ARRAY_SIZE = 8;

extern(C++) struct CTFEFunctionInfo
{
    size_t opcodeStartIndex;
    size_t opcodeEndIndex;

    bool hasBeenGenerated()
    {
        return this.opcodeEndIndex > 0;
    }
}

private struct Pops { size_t amount; bool dynamic; }
private struct Pushes { size_t amount; bool dynamic; }

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

        // Direct loads
        @Pops(0) @Pushes(1) ld_i8Bool,
        @Pops(0) @Pushes(1) ld_i8,
        @Pops(0) @Pushes(1) ld_i16,
        @Pops(0) @Pushes(1) ld_i32,
        @Pops(0) @Pushes(1) ld_i64,
        @Pops(0) @Pushes(1) ld_u8,
        @Pops(0) @Pushes(1) ld_u16,
        @Pops(0) @Pushes(1) ld_u32,
        @Pops(0) @Pushes(1) ld_u64,

        // Primitive conversion functions
        @Pops(1) @Pushes(1) cvt_i8_16,
        @Pops(1) @Pushes(1) cvt_i8_32,
        @Pops(1) @Pushes(1) cvt_i8_64,
        @Pops(1) @Pushes(1) cvt_i16_8,
        @Pops(1) @Pushes(1) cvt_i16_32,
        @Pops(1) @Pushes(1) cvt_i16_64,
        @Pops(1) @Pushes(1) cvt_i32_8,
        @Pops(1) @Pushes(1) cvt_i32_16,
        @Pops(1) @Pushes(1) cvt_i32_64,
        @Pops(1) @Pushes(1) cvt_i64_8,
        @Pops(1) @Pushes(1) cvt_i64_16,
        @Pops(1) @Pushes(1) cvt_i64_32,

        @Pops(1) @Pushes(1) cvt_u8_16,
        @Pops(1) @Pushes(1) cvt_u8_32,
        @Pops(1) @Pushes(1) cvt_u8_64,
        @Pops(1) @Pushes(1) cvt_u16_8,
        @Pops(1) @Pushes(1) cvt_u16_32,
        @Pops(1) @Pushes(1) cvt_u16_64,
        @Pops(1) @Pushes(1) cvt_u32_8,
        @Pops(1) @Pushes(1) cvt_u32_16,
        @Pops(1) @Pushes(1) cvt_u32_64,
        @Pops(1) @Pushes(1) cvt_u64_8,
        @Pops(1) @Pushes(1) cvt_u64_16,
        @Pops(1) @Pushes(1) cvt_u64_32,

        @Pops(1) @Pushes(1) cvt_i8Bool_i8,
        @Pops(1) @Pushes(1) cvt_i8Bool_i16,
        @Pops(1) @Pushes(1) cvt_i8Bool_i32,
        @Pops(1) @Pushes(1) cvt_i8Bool_i64,
        @Pops(1) @Pushes(1) cvt_i8Bool_u8,
        @Pops(1) @Pushes(1) cvt_i8Bool_u16,
        @Pops(1) @Pushes(1) cvt_i8Bool_u32,
        @Pops(1) @Pushes(1) cvt_i8Bool_u64,

        @Pops(1) @Pushes(1) cvt_u_i,
        @Pops(1) @Pushes(1) cvt_i_u,
    }

    @(Instruction.nop) static struct Nop{}
    @(Instruction.call) static struct Call { ushort argCount; FuncDeclaration func; }
    @(Instruction.ret) static struct Return {}

    @(Instruction.copy_frel) static struct CopyFrameRelative { ptrdiff_t stackIndex; }

    @(Instruction.ld_i8Bool) static struct LoadI8Bool{ bool arg; }
    @(Instruction.ld_i8) static struct LoadI8{ byte arg; }
    @(Instruction.ld_i16) static struct LoadI16{ short arg; }
    @(Instruction.ld_i32) static struct LoadI32{ int arg; }
    @(Instruction.ld_i64) static struct LoadI64{ long arg; }
    @(Instruction.ld_u8) static struct LoadU8{ ubyte arg; }
    @(Instruction.ld_u16) static struct LoadU16{ ushort arg; }
    @(Instruction.ld_u32) static struct LoadU32{ uint arg; }
    @(Instruction.ld_u64) static struct LoadU64{ ulong arg; }

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

    @(Instruction.cvt_i8Bool_i8) static struct ConvertI8BoolToI8{ }
    @(Instruction.cvt_i8Bool_i16) static struct ConvertI8BoolToI16{ }
    @(Instruction.cvt_i8Bool_i32) static struct ConvertI8BoolToI32{ }
    @(Instruction.cvt_i8Bool_i64) static struct ConvertI8BoolToI64{ }
    @(Instruction.cvt_i8Bool_u8) static struct ConvertI8BoolToU8{ }
    @(Instruction.cvt_i8Bool_u16) static struct ConvertI8BoolToU16{ }
    @(Instruction.cvt_i8Bool_u32) static struct ConvertI8BoolToU32{ }
    @(Instruction.cvt_i8Bool_u64) static struct ConvertI8BoolToU64{ }

    @(Instruction.cvt_u_i) static struct ConvertUToI{ }
    @(Instruction.cvt_i_u) static struct ConvertIToU{ }

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

    struct StartOfStackFrame {}

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
        @T!(CTFEValue*) valuePtr,

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
}

private struct CTFEVirtualMachine
{
    Array!CTFEOpcode _opcodes;
    Array!CTFEValue  _stack;

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
        assert(func.ctfeInfo.hasBeenGenerated);

        const stackLength = this._stack.length;
        this.push(CTFEValue(CTFEValue.StartOfStackFrame()));
        executeFunction(func.ctfeInfo, ret, this);
        assert(this.pop().type == CTFEValue.Type.startOfFrame);
        assert(this._stack.length == stackLength);
    }
}
private __gshared CTFEVirtualMachine g_ctfeVirtualMachine;

private:

private extern (C++) final class OpcodeCompiler : Visitor
{
    alias visit = Visitor.visit;
    CTFEVirtualMachine* _vm;
    bool _result;

    extern(D) this(CTFEVirtualMachine* vm) @nogc nothrow
    {
        this._vm = vm;
    }

public:

    bool hadErrors()
    {
        return !this._result;
    }

    override void visit(Statement s)
    {
        s.error("statement `%s` cannot be interpreted at compile time", s.toChars());
    }

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

        exp.error("[CTFE2] Unable to compile Expression - unhandled expression type");
        this._result = false;
    }

    override void visit(IntegerExp exp)
    {
        import std;
        writeln("    :: IntegerExp");
        switch(exp.op)
        {
            case EXP.int64:
                if(exp.type == Type.tint8) 
                { 
                    this._vm.appendOpcode(CTFEOpcode.LoadI8(cast(byte)exp.toInteger())); 
                    this._result = true; 
                }
                else if(exp.type == Type.tint16) 
                { 
                    this._vm.appendOpcode(CTFEOpcode.LoadI16(cast(short)exp.toInteger())); 
                    this._result = true; 
                }
                else if(exp.type == Type.tint32) 
                { 
                    this._vm.appendOpcode(CTFEOpcode.LoadI32(cast(int)exp.toInteger())); 
                    this._result = true; 
                }
                else if(exp.type == Type.tint64) 
                { 
                    this._vm.appendOpcode(CTFEOpcode.LoadI64(exp.toInteger())); 
                    this._result = true; 
                }
                else if(exp.type == Type.tbool)
                {
                    this._vm.appendOpcode(CTFEOpcode.LoadI8Bool(exp.toInteger() != 0));
                    this._result = true;
                }
                else
                {
                    exp.error("[CTFE2] Unable to compile IntegerExp - unhandled native integer type");
                    this._result = true; 
                }
                break;
            default:
                exp.error("[CTFE2] Unable to compile IntegerExp - unhandled integer expression type");
                this._result = false; 
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
            this._result = this.tryEmitNumericCast(exp);
            return;
        }

        exp.error("[CTFE] Unable to compile CastExp - Unhandled `to` type");
        this._result = false;
    }

private:

    bool tryEmitNumericCast(CastExp exp)
    {
        import std;
        writeln("        :: tryEmitNumericCast");

        if(exp.e1.type == Type.tbool)
        {
            if(exp.to == Type.tint8) { this._vm.appendOpcode(CTFEOpcode.ConvertI8BoolToI8()); return true; }
            else if(exp.to == Type.tint16) { this._vm.appendOpcode(CTFEOpcode.ConvertI8BoolToI16()); return true; }
            else if(exp.to == Type.tint32) { this._vm.appendOpcode(CTFEOpcode.ConvertI8BoolToI32()); return true; }
            else if(exp.to == Type.tint64) { this._vm.appendOpcode(CTFEOpcode.ConvertI8BoolToI64()); return true; }
            else if(exp.to == Type.tuns8) { this._vm.appendOpcode(CTFEOpcode.ConvertI8BoolToU8()); return true; }
            else if(exp.to == Type.tuns16) { this._vm.appendOpcode(CTFEOpcode.ConvertI8BoolToU16()); return true; }
            else if(exp.to == Type.tuns32) { this._vm.appendOpcode(CTFEOpcode.ConvertI8BoolToU32()); return true; }
            else if(exp.to == Type.tuns64) { this._vm.appendOpcode(CTFEOpcode.ConvertI8BoolToU64()); return true; }
            else
            {
                exp.error("[CTFE2] Unable to compile CastExp - Unhandled boolean target type");
                return false;
            }
        }

        return false;
    }
}

// BOOKMARK: Opcode Compilation
bool compileFunction(scope FuncDeclaration func, scope ref CTFEVirtualMachine vm)
{
    if (func.semanticRun == PASS.semantic3)
    {
        func.error("circular dependency. Functions cannot be interpreted while being compiled");
        return false;
    }
    if (!func.functionSemantic3())
        return false;
    if (func.semanticRun < PASS.semantic3done)
    {
        func.error("circular dependency. Functions cannot be interpreted while being compiled");
        return false;
    }

    return true;
}

bool compileExpressionAsFunction(scope Expression exp, scope ref CTFEVirtualMachine vm, scope ref CTFEFunctionInfo info)
{
    import std;
    writeln(":: compileExpressionAsFunction");
    writeln("    exp: ", exp);

    info.opcodeStartIndex = vm.getOpcodeIndex();

    scope OpcodeCompiler compiler = new OpcodeCompiler(&vm);
    compiler.visit(exp);
    if(compiler.hadErrors)
    {
        writeln("!! compileExpressionAsFunction");
        return false;
    }
    vm.appendOpcode(CTFEOpcode.Return());

    info.opcodeEndIndex = vm.getOpcodeIndex();
    writeln("^^ compileExpressionAsFunction");
    writeln("    info: ", info);
    writeln("    opcodes: ", vm._opcodes[info.opcodeStartIndex..info.opcodeEndIndex]);
    return true;
}

// BOOKMARK: Opcode execution
template IsSpecialInstruction(string instructionName)
{
    alias Instruction = __traits(getMember, CTFEOpcode.Instruction, instructionName);
    
    alias UDAs = __traits(getAttributes, Instruction);
    static assert(is(typeof(UDAs[0]) == Pops));
    static assert(is(typeof(UDAs[1]) == Pushes));

    enum IsSpecialInstruction = UDAs[0].dynamic || UDAs[1].dynamic;
}

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
    Foreach: foreach(i; info.opcodeStartIndex..info.opcodeEndIndex)
    {
        CTFEOpcode op = vm._opcodes[i];
        Switch: final switch(op.instruction) with(CTFEOpcode.Instruction)
        {
            case call:
                break;

            case ret:
                retVal = vm.pop();
                break Foreach;

            static foreach(memberName; __traits(allMembers, CTFEOpcode.Instruction))
            static if(!IsSpecialInstruction!memberName)
            {
                case mixin(memberName):
                    alias FuncName = InstructionFuncName!(__traits(getMember, CTFEOpcode.Instruction, memberName));
                    alias Func     = __traits(getMember, dmd.ctfejit, FuncName);
                    enum PopCount  = InstructionPopCount!memberName;
                    enum PushCount = InstructionPushCount!memberName;

                    CTFEValue[PopCount] inputs;
                    CTFEValue[PushCount] outputs;

                    foreach(ref input; inputs)
                        input = vm.pop();

                    Func(vm, op, inputs, outputs);

                    foreach(output; outputs)
                        vm.push(output);
                    break Switch;
            }
        }
    }
}

// BOOKMARK: Opcode Templates
template InstructionFuncName(alias Instruction)
{
    immutable InstructionFuncName = "ctfe_"~__traits(identifier, Instruction);
}

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

    mixin("@(Instruction) void "~InstructionFuncName!Instruction~"(scope ref CTFEVirtualMachine vm, CTFEOpcode opcode, CTFEValue[PopCount] inputs, scope ref CTFEValue[PushCount] outputs)
    {
        assert(opcode.instruction == InstructionAsValue);

        HandlerParameters params;
        
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
                params[StaticArgs+i] = inputs[i];
            else
                params[StaticArgs+i] = *inputs[i].asPtr!(HandlerParameters[StaticArgs+i]*);
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
    }");
}

// BOOKMARK: Handler Generation
static foreach(memberName; __traits(allMembers, dmd.ctfejit))
static if(memberName.length >= 7 && memberName[0..7] == "opcode_")
    mixin OpcodeHandler!memberName;

// BOOKMARK: Opcode Implementation
@(CTFEOpcode.Instruction.nop) void opcode_nop(CTFEOpcode.Nop op) {}

@(CTFEOpcode.Instruction.copy_frel) void opcode_copy_frel(scope CTFEVirtualMachine* vm, CTFEOpcode.CopyFrameRelative op, scope CTFEValue* r1)
{
    const start = vm.getIndexOfStackFrameStart();
    *r1 = vm.get(start + op.stackIndex);
}

@(CTFEOpcode.Instruction.ld_i8Bool) void opcode_ld_i8Bool(CTFEOpcode.LoadI8Bool op, scope bool* r1) { *r1 = op.arg; }
@(CTFEOpcode.Instruction.ld_i8) void opcode_ld_i8(CTFEOpcode.LoadI8 op, scope byte* r1) { *r1 = op.arg; }
@(CTFEOpcode.Instruction.ld_i16) void opcode_ld_i16(CTFEOpcode.LoadI16 op, scope short* r1) { *r1 = op.arg; }
@(CTFEOpcode.Instruction.ld_i32) void opcode_ld_i32(CTFEOpcode.LoadI32 op, scope int* r1) { *r1 = op.arg; }
@(CTFEOpcode.Instruction.ld_i64) void opcode_ld_i64(CTFEOpcode.LoadI64 op, scope long* r1) { *r1 = op.arg; }
@(CTFEOpcode.Instruction.ld_u8) void opcode_ld_u8(CTFEOpcode.LoadU8 op, scope ubyte* r1) { *r1 = op.arg; }
@(CTFEOpcode.Instruction.ld_u16) void opcode_ld_u16(CTFEOpcode.LoadU16 op, scope ushort* r1) { *r1 = op.arg; }
@(CTFEOpcode.Instruction.ld_u32) void opcode_ld_u32(CTFEOpcode.LoadU32 op, scope uint* r1) { *r1 = op.arg; }
@(CTFEOpcode.Instruction.ld_u64) void opcode_ld_u64(CTFEOpcode.LoadU64 op, scope ulong* r1) { *r1 = op.arg; }

@(CTFEOpcode.Instruction.cvt_i8_16) void opcode_cvt_i8_16(CTFEOpcode.ConvertI8To16 op, byte i1, scope short* r1){ *r1 = cast(short)i1; }
@(CTFEOpcode.Instruction.cvt_i8_32) void opcode_cvt_i8_32(CTFEOpcode.ConvertI8To32 op, byte i1, scope int* r1){ *r1 = cast(int)i1; }
@(CTFEOpcode.Instruction.cvt_i8_64) void opcode_cvt_i8_64(CTFEOpcode.ConvertI8To64 op, byte i1, scope long* r1){ *r1 = cast(long)i1; }
@(CTFEOpcode.Instruction.cvt_i16_8) void opcode_cvt_i16_8(CTFEOpcode.ConvertI16To8 op, short i1, scope byte* r1){ *r1 = cast(byte)i1; }
@(CTFEOpcode.Instruction.cvt_i16_32) void opcode_cvt_i16_32(CTFEOpcode.ConvertI16To32 op, short i1, scope int* r1){ *r1 = cast(int)i1; }
@(CTFEOpcode.Instruction.cvt_i16_64) void opcode_cvt_i16_64(CTFEOpcode.ConvertI16To64 op, short i1, scope long* r1){ *r1 = cast(long)i1; }
@(CTFEOpcode.Instruction.cvt_i32_8) void opcode_cvt_i32_8(CTFEOpcode.ConvertI32To8 op, int i1, scope byte* r1){ *r1 = cast(byte)i1; }
@(CTFEOpcode.Instruction.cvt_i32_16) void opcode_cvt_i32_16(CTFEOpcode.ConvertI32To16 op, int i1, scope short* r1){ *r1 = cast(short)i1; }
@(CTFEOpcode.Instruction.cvt_i32_64) void opcode_cvt_i32_64(CTFEOpcode.ConvertI32To64 op, int i1, scope long* r1){ *r1 = cast(long)i1; }
@(CTFEOpcode.Instruction.cvt_i64_8) void opcode_cvt_i64_8(CTFEOpcode.ConvertI64To8 op, long i1, scope byte* r1){ *r1 = cast(byte)i1; }
@(CTFEOpcode.Instruction.cvt_i64_16) void opcode_cvt_i64_16(CTFEOpcode.ConvertI64To16 op, long i1, scope short* r1){ *r1 = cast(short)i1; }
@(CTFEOpcode.Instruction.cvt_i64_32) void opcode_cvt_i64_32(CTFEOpcode.ConvertI64To32 op, long i1, scope int* r1){ *r1 = cast(int)i1; }

@(CTFEOpcode.Instruction.cvt_u8_16) void opcode_cvt_u8_16(CTFEOpcode.ConvertU8To16 op, ubyte i1, scope ushort* r1){ *r1 = cast(ushort)i1; }
@(CTFEOpcode.Instruction.cvt_u8_32) void opcode_cvt_u8_32(CTFEOpcode.ConvertU8To32 op, ubyte i1, scope uint* r1){ *r1 = cast(uint)i1; }
@(CTFEOpcode.Instruction.cvt_u8_64) void opcode_cvt_u8_64(CTFEOpcode.ConvertU8To64 op, ubyte i1, scope ulong* r1){ *r1 = cast(ulong)i1; }
@(CTFEOpcode.Instruction.cvt_u16_8) void opcode_cvt_u16_8(CTFEOpcode.ConvertU16To8 op, ushort i1, scope ubyte* r1){ *r1 = cast(ubyte)i1; }
@(CTFEOpcode.Instruction.cvt_u16_32) void opcode_cvt_u16_32(CTFEOpcode.ConvertU16To32 op, ushort i1, scope uint* r1){ *r1 = cast(uint)i1; }
@(CTFEOpcode.Instruction.cvt_u16_64) void opcode_cvt_u16_64(CTFEOpcode.ConvertU16To64 op, ushort i1, scope ulong* r1){ *r1 = cast(ulong)i1; }
@(CTFEOpcode.Instruction.cvt_u32_8) void opcode_cvt_u32_8(CTFEOpcode.ConvertU32To8 op, uint i1, scope ubyte* r1){ *r1 = cast(ubyte)i1; }
@(CTFEOpcode.Instruction.cvt_u32_16) void opcode_cvt_u32_16(CTFEOpcode.ConvertU32To16 op, uint i1, scope ushort* r1){ *r1 = cast(ushort)i1; }
@(CTFEOpcode.Instruction.cvt_u32_64) void opcode_cvt_u32_64(CTFEOpcode.ConvertU32To64 op, uint i1, scope ulong* r1){ *r1 = cast(ulong)i1; }
@(CTFEOpcode.Instruction.cvt_u64_8) void opcode_cvt_u64_8(CTFEOpcode.ConvertU64To8 op, ulong i1, scope ubyte* r1){ *r1 = cast(ubyte)i1; }
@(CTFEOpcode.Instruction.cvt_u64_16) void opcode_cvt_u64_16(CTFEOpcode.ConvertU64To16 op, ulong i1, scope ushort* r1){ *r1 = cast(ushort)i1; }
@(CTFEOpcode.Instruction.cvt_u64_32) void opcode_cvt_u64_32(CTFEOpcode.ConvertU64To32 op, ulong i1, scope uint* r1){ *r1 = cast(uint)i1; }

@(CTFEOpcode.Instruction.cvt_i8Bool_i8) void opcode_cvt_i8Bool_i8(CTFEOpcode.ConvertI8BoolToI8 op, bool i1, scope byte* r1){ *r1 = cast(byte)i1; }
@(CTFEOpcode.Instruction.cvt_i8Bool_i16) void opcode_cvt_i8Bool_i16(CTFEOpcode.ConvertI8BoolToI16 op, bool i1, scope short* r1){ *r1 = cast(short)i1; }
@(CTFEOpcode.Instruction.cvt_i8Bool_i32) void opcode_cvt_i8Bool_i32(CTFEOpcode.ConvertI8BoolToI32 op, bool i1, scope int* r1){ *r1 = cast(int)i1; }
@(CTFEOpcode.Instruction.cvt_i8Bool_i64) void opcode_cvt_i8Bool_i64(CTFEOpcode.ConvertI8BoolToI64 op, bool i1, scope long* r1){ *r1 = cast(long)i1; }
@(CTFEOpcode.Instruction.cvt_i8Bool_u8) void opcode_cvt_i8Boolui8(CTFEOpcode.ConvertI8BoolToU8 op, bool i1, scope ubyte* r1){ *r1 = cast(ubyte)i1; }
@(CTFEOpcode.Instruction.cvt_i8Bool_u16) void opcode_cvt_i8Bool_u16(CTFEOpcode.ConvertI8BoolToU16 op, bool i1, scope ushort* r1){ *r1 = cast(ushort)i1; }
@(CTFEOpcode.Instruction.cvt_i8Bool_u32) void opcode_cvt_i8Bool_u32(CTFEOpcode.ConvertI8BoolToU32 op, bool i1, scope uint* r1){ *r1 = cast(uint)i1; }
@(CTFEOpcode.Instruction.cvt_i8Bool_u64) void opcode_cvt_i8Bool_u64(CTFEOpcode.ConvertI8BoolToU64 op, bool i1, scope ulong* r1){ *r1 = cast(ulong)i1; }

@(CTFEOpcode.Instruction.cvt_u_i) void opcode_cvt_u_i(CTFEOpcode.ConvertUToI op, CTFEValue i1, scope CTFEValue* r1)
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

@(CTFEOpcode.Instruction.cvt_i_u) void opcode_cvt_i_u(CTFEOpcode.ConvertIToU op, CTFEValue i1, scope CTFEValue* r1)
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

void _opcode_call(CTFEOpcode.Call op, scope ref CTFEVirtualMachine vm)
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