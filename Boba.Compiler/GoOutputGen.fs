namespace Boba.Compiler

module GoOutputGen =

    open System
    open System.IO
    open Mochi.Core.Instructions

    let writeHeader (stream: StreamWriter) =
        stream.WriteLine("package main")
        stream.WriteLine("")
        stream.WriteLine("import (")
        stream.WriteLine("    \"os\"")
        stream.WriteLine("    \"github.com/glossopoeia/boba/runtime\"")
        stream.WriteLine(")")
        stream.WriteLine("")
        stream.WriteLine("func main() {")
        stream.WriteLine("    vm := runtime.NewDebugMachine()")

    let writeFooter (stream: StreamWriter) =
        stream.WriteLine("    result := vm.RunFromStart()")
        stream.WriteLine("    os.Exit(int(result))")
        stream.WriteLine("}")

    let writeIByte (stream: StreamWriter) item =
        stream.WriteLine("    vm.WriteI8(" + item.ToString() + ", 0);")

    let writeByte (stream: StreamWriter) item =
        stream.WriteLine("    vm.WriteU8(" + item.ToString() + ", 0);")

    let writeShort (stream: StreamWriter) item =
        stream.WriteLine("    vm.WriteI16(" + item.ToString() + ", 0);")

    let writeUShort (stream: StreamWriter) item =
        stream.WriteLine("    vm.WriteU16(" + item.ToString() + ", 0);")
    
    let writeInt (stream: StreamWriter) item =
        stream.WriteLine("    vm.WriteI32(" + item.ToString() + ", 0);")

    let writeUInt (stream: StreamWriter) item =
        stream.WriteLine("    vm.WriteU32(" + item.ToString() + ", 0);")
    
    let writeLong (stream: StreamWriter) item =
        stream.WriteLine("    vm.WriteI64(" + item.ToString() + ", 0);")

    let writeULong (stream: StreamWriter) item =
        stream.WriteLine("    vm.WriteU64(" + item.ToString() + ", 0);")
    
    let intSizeToMochi size =
        match size with
        | I8 -> "runtime.I8"
        | U8 -> "runtime.U8"
        | I16 -> "runtime.I16"
        | U16 -> "runtime.U16"
        | I32 -> "runtime.I32"
        | U32 -> "runtime.U32"
        | I64 -> "runtime.I64"
        | U64 -> "runtime.U64"
    
    let floatSizeToMochi size =
        match size with
        | Single -> "runtime.SINGLE"
        | Double -> "runtime.DOUBLE"

    let writeIntOp (stream: StreamWriter) op intSize =
        writeByte stream op
        writeByte stream (intSizeToMochi intSize)
    
    let writeFloatOp (stream: StreamWriter) op floatSize =
        writeByte stream op
        writeByte stream (floatSizeToMochi floatSize)

    let writeConvOp (stream: StreamWriter) from into =
        writeByte stream "runtime.VALUE_CONV"
        writeByte stream from
        writeByte stream into

    let getLocationBytes (labels: Map<string, int>) target =
        match target with
        | Label s -> labels.[s].ToString()
        | Index _ -> failwith "getLocationBytes does not support explicit indexes yet."

    let writeInstruction stream labels instr =
        match instr with
        | INop -> writeByte stream "runtime.NOP"
        | IBreakpoint -> writeByte stream "runtime.BREAKPOINT"
        | IAbort ->
            writeByte stream "runtime.ABORT"
        | IConstant i ->
            writeByte stream "runtime.CONSTANT"
            writeUShort stream i
        | IOffset rel ->
            writeByte stream "runtime.OFFSET"
            writeInt stream rel
        | IReturn -> writeByte stream "runtime.RETURN"
        | ICall loc ->
            writeByte stream "runtime.CALL"
            writeUInt stream (getLocationBytes labels loc)
        | ITailCall loc ->
            writeByte stream "runtime.TAILCALL"
            writeUInt stream (getLocationBytes labels loc)
        | IStore amt ->
            writeByte stream "runtime.STORE"
            writeByte stream amt
        | IOverwrite (frame, slot) ->
            writeByte stream "runtime.OVERWRITE"
            writeUShort stream frame
            writeUShort stream slot
        | IForget -> writeByte stream "runtime.FORGET"
        | IFind (frame, slot) ->
            writeByte stream "runtime.FIND"
            writeUShort stream frame
            writeUShort stream slot
        | ICallClosure -> writeByte stream "runtime.CALL_CLOSURE"
        | ITailCallClosure -> writeByte stream "runtime.TAILCALL_CLOSURE"
        | IClosure (body, args, closed) ->
            writeByte stream "runtime.CLOSURE"
            writeUInt stream (getLocationBytes labels body)
            writeByte stream args
            writeUShort stream closed.Length
            closed |> Seq.iter (fun (f, i) -> writeUShort stream f; writeUShort stream i)
        | IRecursive (body, args, closed) ->
            writeByte stream "runtime.RECURSIVE"
            writeUInt stream body
            writeByte stream args
            writeUShort stream closed.Length
            closed |> Seq.iter (fun (f, i) -> writeUShort stream f; writeUShort stream i)
        | IMutual n ->
            writeByte stream "runtime.MUTUAL"
            writeByte stream n
        | IHandle (id, after, args, ops) ->
            writeByte stream "runtime.HANDLE"
            writeShort stream after
            writeUInt stream id
            writeByte stream args
            writeByte stream ops
        | IInject handleId ->
            writeByte stream "runtime.INJECT"
            writeUInt stream handleId
        | IEject handleId ->
            writeByte stream "runtime.EJECT"
            writeUInt stream handleId
        | IComplete -> writeByte stream "runtime.COMPLETE"
        | IEscape (handleId, handlerIdx) ->
            writeByte stream "runtime.ESCAPE"
            writeUInt stream handleId
            writeByte stream handlerIdx
        | ICallContinuation -> writeByte stream "runtime.CALL_CONTINUATION"
        | ITailCallContinuation -> writeByte stream "runtime.TAILCALL_CONTINUATION"
        | IJumpIf target ->
            writeByte stream "runtime.JUMP_TRUE"
            writeUInt stream (getLocationBytes labels target)
        | IOffsetIf rel ->
            writeByte stream "runtime.OFFSET_TRUE"
            writeInt stream rel

        | IEmptyRecord -> writeByte stream "runtime.RECORD_NIL"
        | IRecordExtend l ->
            writeByte stream "runtime.RECORD_EXTEND"
            writeInt stream l
        | IRecordRestrict l ->
            writeByte stream "runtime.RECORD_RESTRICT"
            writeInt stream l
        | IRecordSelect l ->
            writeByte stream "runtime.RECORD_SELECT"
            writeInt stream l
        | IRecordUpdate l ->
            writeByte stream "runtime.RECORD_UPDATE"
            writeInt stream l
        
        | IVariant l ->
            writeByte stream "runtime.VARIANT"
            writeInt stream l
        | IVariantEmbed l ->
            writeByte stream "runtime.EMBED"
            writeInt stream l
        | IIsCase l ->
            writeByte stream "runtime.IS_CASE"
            writeInt stream l
        | IJumpCase (l, target) ->
            writeByte stream "runtime.JUMP_CASE"
            writeInt stream l
            writeUInt stream (getLocationBytes labels target)
        | IOffsetCase (l, rel) ->
            writeByte stream "runtime.OFFSET_CASE"
            writeInt stream l
            writeInt stream rel
        
        | ISwap -> writeByte stream "runtime.SWAP"
        | IDup -> writeByte stream "runtime.DUP"
        | IZap -> writeByte stream "runtime.ZAP"
        
        | ITrue -> writeByte stream "runtime.TRUE"
        | IFalse -> writeByte stream "runtime.FALSE"
        | IBoolNot -> writeByte stream "runtime.BOOL_NOT"
        | IBoolAnd -> writeByte stream "runtime.BOOL_AND"
        | IBoolOr -> writeByte stream "runtime.BOOL_OR"
        | IBoolXor -> writeByte stream "runtime.BOOL_NEQ"
        | IBoolEq -> writeByte stream "runtime.BOOL_EQ"

        | II8 v ->
            writeByte stream "runtime.I8"
            writeIByte stream v
        | IU8 v ->
            writeByte stream "runtime.U8"
            writeByte stream v
        | II16 v ->
            writeByte stream "runtime.I16"
            writeShort stream v
        | IU16 v ->
            writeByte stream "runtime.U16"
            writeUShort stream v
        | II32 v ->
            writeByte stream "runtime.I32"
            writeInt stream v
        | IU32 v ->
            writeByte stream "runtime.U32"
            writeUInt stream v
        | II64 v ->
            writeByte stream "runtime.I64"
            writeLong stream v
        | IU64 v ->
            writeByte stream "runtime.U64"
            writeULong stream v
        | ISingle v ->
            writeByte stream "runtime.SINGLE"
            let intrepr = BitConverter.SingleToUInt32Bits v
            writeUInt stream intrepr
        | IDouble v ->
            writeByte stream "runtime.DOUBLE"
            let intrepr = BitConverter.DoubleToUInt64Bits v
            writeULong stream intrepr

        | IConvBoolInt size -> writeConvOp stream "runtime.BOOL" (intSizeToMochi size)
        | IConvIntBool size -> writeConvOp stream (intSizeToMochi size) "runtime.BOOL"
        | IConvBoolFloat size -> writeConvOp stream "runtime.BOOL" (floatSizeToMochi size)
        | IConvFloatBool size -> writeConvOp stream (floatSizeToMochi size) "runtime.BOOL"
        | IConvIntInt (s1, s2) -> writeConvOp stream (intSizeToMochi s1) (intSizeToMochi s2)
        | IConvIntFloat (s1, s2) -> writeConvOp stream (intSizeToMochi s1) (floatSizeToMochi s2)
        | IConvFloatInt (s1, s2) -> writeConvOp stream (floatSizeToMochi s1) (intSizeToMochi s2)
        | IConvFloatFloat (s1, s2) -> writeConvOp stream (floatSizeToMochi s1) (floatSizeToMochi s2)

        | IIntNeg size -> writeIntOp stream "runtime.NUM_NEG" size
        | IIntInc size -> writeIntOp stream "runtime.NUM_INC" size
        | IIntDec size -> writeIntOp stream "runtime.NUM_DEC" size
        | IIntAdd size -> writeIntOp stream "runtime.NUM_ADD" size
        | IIntSub size -> writeIntOp stream "runtime.NUM_SUB" size
        | IIntMul size -> writeIntOp stream "runtime.NUM_MUL" size
        | IIntDivRemT size -> writeIntOp stream "runtime.NUM_DIV_REM_T" size
        | IIntDivRemF size -> writeIntOp stream "runtime.NUM_DIV_REM_F" size
        | IIntDivRemE size -> writeIntOp stream "runtime.NUM_DIV_REM_E" size
        | IIntOr size -> writeIntOp stream "runtime.INT_OR" size
        | IIntAnd size -> writeIntOp stream "runtime.INT_AND" size
        | IIntXor size -> writeIntOp stream "runtime.INT_XOR" size
        | IIntComplement size -> writeIntOp stream "runtime.INT_COMP" size
        | IIntShiftLeft size -> writeIntOp stream "runtime.INT_SHL" size
        | IIntLogicShiftRight size -> writeIntOp stream "runtime.INT_SHR" size
        | IIntEqual size -> writeIntOp stream "runtime.NUM_EQ" size
        | IIntLessThan size -> writeIntOp stream "runtime.NUM_LT" size
        | IIntGreaterThan size -> writeIntOp stream "runtime.NUM_GT" size
        | IIntSign size -> writeIntOp stream "runtime.NUM_SIGN" size

        | IFloatNeg size -> writeFloatOp stream "runtime.NUM_NEG" size
        | IFloatAdd size -> writeFloatOp stream "runtime.NUM_ADD" size
        | IFloatSub size -> writeFloatOp stream "runtime.NUM_SUB" size
        | IFloatMul size -> writeFloatOp stream "runtime.NUM_MUL" size
        | IFloatDiv size -> writeFloatOp stream "runtime.NUM_DIV_REM_T" size
        | IFloatEqual size -> writeFloatOp stream "runtime.NUM_EQ" size
        | IFloatLess size -> writeFloatOp stream "runtime.NUM_LT" size
        | IFloatGreater size -> writeFloatOp stream "runtime.NUM_GT" size
        | IFloatSign size -> writeFloatOp stream "runtime.NUM_SIGN" size

        | IListNil -> writeByte stream "runtime.LIST_NIL"
        | IListCons -> writeByte stream "runtime.LIST_CONS"
        | IListHead -> writeByte stream "runtime.LIST_HEAD"
        | IListTail -> writeByte stream "runtime.LIST_TAIL"
        | IListAppend -> writeByte stream "runtime.LIST_APPEND"

        | IStringConcat -> writeByte stream "runtime.STRING_CONCAT"
        | IPrint -> writeByte stream "runtime.PRINT"

        | IStringPlaceholder _ -> failwith "Bytecode generation encountered a placeholder that should have been removed."

    let writeLabel (stream: StreamWriter) labelIdx labelText =
        stream.WriteLine("    vm.AddLabel(\"" + labelText + "\", " + labelIdx.ToString() + ")")

    let writeConstant (stream: StreamWriter) constant =
        match constant with
        | IStringPlaceholder s ->
            stream.WriteLine("    vm.AddConstant(\"" + s + "\")")
        | _ -> failwith "Tried to write a non-constant as a constant."

    let writeConstants stream consts =
        consts |> Seq.iter (writeConstant stream)

    let writeBytecode stream (bytecode: LabeledBytecode) =
        bytecode.Instructions |> Seq.iter (writeInstruction stream bytecode.Labels)
        bytecode.Labels |> Seq.iter (fun l -> writeLabel stream l.Value l.Key)

    let writeBlocks stream blocks consts =
        writeHeader stream
        writeConstants stream consts
        writeBytecode stream (delabelBytes blocks)
        writeFooter stream

    let writeAndRunDebug blocks consts =
        let sw = new StreamWriter("./main.go")
        writeBlocks sw blocks consts
        sw.Flush()

        let runRes = Shell.executeCommand "go" ["run"; "."] |> Async.RunSynchronously
        if runRes.ExitCode = 0
        then
            printfn "%s" runRes.StandardOutput
            printfn "App ran successfully"
        else
            printfn "%s" runRes.StandardError
            printfn "App run failed"
        runRes.ExitCode