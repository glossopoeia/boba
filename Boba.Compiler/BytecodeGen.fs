namespace Boba.Compiler

module BytecodeGen =

    open System
    open System.IO
    open Boba.Compiler.MochiGen
    open Boba.Core.Common
    open Mochi.Core
    open Mochi.Core.Instructions

    let writeHeader (stream: StreamWriter) =
        stream.WriteLine("#include <stdio.h>")
        stream.WriteLine("#include <stdlib.h>")
        stream.WriteLine("#include \"debug.h\"")
        stream.WriteLine("int main(int argc, const char* argv[]) {")
        stream.WriteLine("    MochiVM* vm = mochiNewVM(NULL);")

    let writeFooter (stream: StreamWriter) =
        stream.WriteLine("    int res = mochiInterpret(vm);")
        stream.WriteLine("    mochiFreeVM(vm);")
        stream.WriteLine("    return res;")
        stream.WriteLine("}")

    let writeByte (stream: StreamWriter) item =
        stream.WriteLine("    mochiWriteCodeByte(vm, " + item.ToString() + ", 0);")

    let writeShort (stream: StreamWriter) item =
        stream.WriteLine("    mochiWriteCodeI16(vm, " + item.ToString() + ", 0);")

    let writeUShort (stream: StreamWriter) item =
        stream.WriteLine("    mochiWriteCodeU16(vm, " + item.ToString() + ", 0);")
    
    let writeInt (stream: StreamWriter) item =
        stream.WriteLine("    mochiWriteCodeI32(vm, " + item.ToString() + ", 0);")

    let writeUInt (stream: StreamWriter) item =
        stream.WriteLine("    mochiWriteCodeU32(vm, " + item.ToString() + ", 0);")

    let getLocationBytes (labels: Map<string, int>) target =
        match target with
        | Label s -> labels.[s].ToString()
        | Index _ -> failwith "getLocationBytes does not support explicit indexes yet."

    let writeInstruction stream labels instr =
        match instr with
        | INop -> writeByte stream "CODE_NOP"
        | IBreakpoint -> writeByte stream "CODE_BREAKPOINT"
        | IAbort r ->
            writeByte stream "CODE_ABORT"
            writeByte stream (r.ToString())
        | IConstant i ->
            writeByte stream "CODE_CONSTANT"
            writeUShort stream i
        | IOffset rel ->
            writeByte stream "CODE_OFFSET"
            writeInt stream rel
        | IReturn -> writeByte stream "CODE_RETURN"
        | ICall loc ->
            writeByte stream "CODE_CALL"
            writeUInt stream (getLocationBytes labels loc)
        | ITailCall loc ->
            writeByte stream "CODE_TAILCALL"
            writeUInt stream (getLocationBytes labels loc)
        | IStore amt ->
            writeByte stream "CODE_STORE"
            writeByte stream amt
        | IOverwrite (frame, slot) ->
            writeByte stream "CODE_OVERWRITE"
            writeUShort stream frame
            writeUShort stream slot
        | IForget -> writeByte stream "CODE_FORGET"
        | IFind (frame, slot) ->
            writeByte stream "CODE_FIND"
            writeUShort stream frame
            writeUShort stream slot
        | ICallClosure -> writeByte stream "CODE_CALL_CLOSURE"
        | ITailCallClosure -> writeByte stream "CODE_TAILCALL_CLOSURE"
        | IClosure (body, args, closed) ->
            writeByte stream "CODE_CLOSURE"
            writeUInt stream (getLocationBytes labels body)
            writeByte stream args
            writeUShort stream closed.Length
            closed |> Seq.iter (fun (f, i) -> writeUShort stream f; writeUShort stream i)
        | IRecursive (body, args, closed) ->
            writeByte stream "CODE_RECURSIVE"
            writeUInt stream body
            writeByte stream args
            writeUShort stream closed.Length
            closed |> Seq.iter (fun (f, i) -> writeUShort stream f; writeUShort stream i)
        | IMutual n ->
            writeByte stream "CODE_MUTUAL"
            writeByte stream n
        | IHandle (id, after, args, ops) ->
            writeByte stream "CODE_HANDLE"
            writeShort stream after
            writeUInt stream id
            writeByte stream args
            writeByte stream ops
        | IInject handleId ->
            writeByte stream "CODE_INJECT"
            writeUInt stream handleId
        | IEject handleId ->
            writeByte stream "CODE_INJECT"
            writeUInt stream handleId
        | IComplete -> writeByte stream "CODE_COMPLETE"
        | IEscape (handleId, handlerIdx) ->
            writeByte stream "CODE_ESCAPE"
            writeUInt stream handleId
            writeByte stream handlerIdx
        | ICallContinuation -> writeByte stream "CODE_CALL_CONTINUATION"
        | ITailCallContinuation -> writeByte stream "CODE_TAILCALL_CONTINUATION"
        | IJumpIf target ->
            writeByte stream "CODE_JUMP_TRUE"
            writeUInt stream (getLocationBytes labels target)
        | IOffsetIf rel ->
            writeByte stream "CODE_OFFSET_TRUE"
            writeUInt stream rel
        
        | ITrue -> writeByte stream "CODE_TRUE"
        | IFalse -> writeByte stream "CODE_FALSE"
        | IBoolNot -> writeByte stream "CODE_BOOL_NOT"
        | IBoolAnd -> writeByte stream "CODE_BOOL_AND"
        | IBoolOr -> writeByte stream "CODE_BOOL_OR"
        | IBoolXor -> writeByte stream "CODE_BOOL_NEQ"
        | IBoolEq -> writeByte stream "CODE_BOOL_EQ"

        | IListNil -> writeByte stream "CODE_LIST_NIL"
        | IListCons -> writeByte stream "CODE_LIST_CONS"
        | IListHead -> writeByte stream "CODE_LIST_HEAD"
        | IListTail -> writeByte stream "CODE_LIST_TAIL"
        | IListAppend -> writeByte stream "CODE_LIST_APPEND"

    let writeLabel (stream: StreamWriter) labelIdx labelText =
        stream.WriteLine("    mochiWriteLabel(vm, " + labelIdx.ToString() + ", \"" + labelText + "\");")

    let writeBytecode stream (bytecode: LabeledBytecode) =
        writeHeader stream
        bytecode.Instructions |> Seq.iter (writeInstruction stream bytecode.Labels)
        bytecode.Labels |> Seq.iter (fun l -> writeLabel stream l.Value l.Key)
        writeFooter stream

    let writeBlocks stream blocks =
        writeBytecode stream (delabelBytes blocks)