namespace Boba.Compiler

module COutputGen =

    open System
    open System.IO
    open Mochi.Core.Instructions

    let writeHeader (stream: StreamWriter) =
        stream.WriteLine("#include <stdio.h>")
        stream.WriteLine("#include <stdlib.h>")
        stream.WriteLine("#include \"debug.h\"")
        stream.WriteLine("int main(int argc, const char* argv[]) {")
        stream.WriteLine("    MochiVM* vm = mochiNewVM(NULL);")

    let writeFooter (stream: StreamWriter) =
        stream.WriteLine("    int res = mochiRun(vm, 0, NULL);")
        stream.WriteLine("    mochiFreeVM(vm);")
        stream.WriteLine("    return res;")
        stream.WriteLine("}")

    let writeIByte (stream: StreamWriter) item =
        stream.WriteLine("    mochiWriteCodeI8(vm, " + item.ToString() + ", 0);")

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
    
    let writeLong (stream: StreamWriter) item =
        stream.WriteLine("    mochiWriteCodeI64(vm, " + item.ToString() + ", 0);")

    let writeULong (stream: StreamWriter) item =
        stream.WriteLine("    mochiWriteCodeU64(vm, " + item.ToString() + ", 0);")
    
    let intSizeToMochi size =
        match size with
        | I8 -> "VAL_I8"
        | U8 -> "VAL_U8"
        | I16 -> "VAL_I16"
        | U16 -> "VAL_U16"
        | I32 -> "VAL_I32"
        | U32 -> "VAL_U32"
        | I64 -> "VAL_I64"
        | U64 -> "VAL_U64"
    
    let floatSizeToMochi size =
        match size with
        | Single -> "VAL_SINGLE"
        | Double -> "VAL_DOUBLE"

    let writeIntOp (stream: StreamWriter) op intSize =
        writeByte stream op
        writeByte stream (intSizeToMochi intSize)

    let writeConvOp (stream: StreamWriter) from into =
        writeByte stream "CODE_VALUE_CONV"
        writeByte stream from
        writeByte stream into

    let getLocationBytes (labels: Map<string, int>) target =
        match target with
        | Label s -> labels.[s].ToString()
        | Index _ -> failwith "getLocationBytes does not support explicit indexes yet."

    let writeInstruction stream labels instr =
        match instr with
        | INop -> writeByte stream "CODE_NOP"
        | IBreakpoint -> writeByte stream "CODE_BREAKPOINT"
        | IAbort ->
            writeByte stream "CODE_ABORT"
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
        | IOverwrite ind ->
            writeByte stream "CODE_OVERWRITE"
            writeUInt stream ind
        //| IForget -> writeByte stream "CODE_FORGET"
        //| IFind (frame, slot) ->
        //    writeByte stream "CODE_FIND"
        //    writeUShort stream frame
        //    writeUShort stream slot
        | ICallClosure -> writeByte stream "CODE_CALL_CLOSURE"
        | ITailCallClosure -> writeByte stream "CODE_TAILCALL_CLOSURE"
        //| IClosure (body, args, closed) ->
        //    writeByte stream "CODE_CLOSURE"
        //    writeUInt stream (getLocationBytes labels body)
        //    writeByte stream args
        //    writeUShort stream closed.Length
            //closed |> Seq.iter (fun (f, i) -> writeUShort stream f; writeUShort stream i)
        //| IRecursive (body, args, closed) ->
        //    writeByte stream "CODE_RECURSIVE"
        //    writeUInt stream body
        //    writeByte stream args
        //    writeUShort stream closed.Length
            //closed |> Seq.iter (fun (f, i) -> writeUShort stream f; writeUShort stream i)
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
            writeByte stream "CODE_EJECT"
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
            writeInt stream rel

        | IEmptyRecord -> writeByte stream "CODE_RECORD_NIL"
        | IRecordExtend l ->
            writeByte stream "CODE_RECORD_EXTEND"
            writeUInt stream l
        | IRecordSelect l ->
            writeByte stream "CODE_RECORD_SELECT"
            writeUInt stream l
        
        | IVariant l ->
            writeByte stream "CODE_VARIANT"
            writeUInt stream l
        | IIsCase l ->
            writeByte stream "CODE_IS_CASE"
            writeUInt stream l
        | IJumpCase (l, target) ->
            writeByte stream "CODE_JUMP_CASE"
            writeUInt stream l
            writeUInt stream (getLocationBytes labels target)
        | IOffsetCase (l, rel) ->
            writeByte stream "CODE_OFFSET_CASE"
            writeUInt stream l
            writeInt stream rel
        
        | II8 v ->
            writeByte stream "CODE_I8"
            writeIByte stream v
        | IU8 v ->
            writeByte stream "CODE_U8"
            writeByte stream v
        | II16 v ->
            writeByte stream "CODE_I16"
            writeShort stream v
        | IU16 v ->
            writeByte stream "CODE_U16"
            writeUShort stream v
        | II32 v ->
            writeByte stream "CODE_I32"
            writeInt stream v
        | IU32 v ->
            writeByte stream "CODE_U32"
            writeUInt stream v
        | II64 v ->
            writeByte stream "CODE_I64"
            writeLong stream v
        | IU64 v ->
            writeByte stream "CODE_U64"
            writeULong stream v
        | ISingle v ->
            writeByte stream "CODE_SINGLE"
            let intrepr = BitConverter.SingleToUInt32Bits v
            writeUInt stream intrepr
        | IDouble v ->
            writeByte stream "CODE_DOUBLE"
            let intrepr = BitConverter.DoubleToUInt64Bits v
            writeULong stream intrepr

        | IListNil -> writeByte stream "CODE_LIST_NIL"
        | IListCons -> writeByte stream "CODE_LIST_CONS"
        | IListHead -> writeByte stream "CODE_LIST_HEAD"
        | IListTail -> writeByte stream "CODE_LIST_TAIL"
        | IListAppend -> writeByte stream "CODE_LIST_APPEND"

        | IStringConcat -> writeByte stream "CODE_STRING_CONCAT"
        | IPrint -> writeByte stream "CODE_PRINT"

        | IStringPlaceholder _ -> failwith "Bytecode generation encountered a placeholder that should have been removed."

    let writeLabel (stream: StreamWriter) labelIdx labelText =
        stream.WriteLine("    mochiWriteLabel(vm, " + labelIdx.ToString() + ", \"" + labelText + "\");")

    let writeConstant (stream: StreamWriter) constant =
        match constant with
        | IStringPlaceholder s ->
            stream.WriteLine("    mochiWriteStringConst(vm, \"" + s + "\");")
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
    
    let rec copyDirRec src dest =
        if not <| Directory.Exists(dest) then
            Directory.CreateDirectory(dest) |> ignore

        let srcDir = DirectoryInfo(src)

        for file in srcDir.GetFiles() do
            let temppath = System.IO.Path.Combine(dest, file.Name)
            file.CopyTo(temppath, true) |> ignore

        for subdir in srcDir.GetDirectories() do
            let dstSubDir = System.IO.Path.Combine(dest, subdir.Name)
            copyDirRec subdir.FullName dstSubDir

    let writeAndRunDebug blocks consts =
        copyDirRec "./mochivm" "./output"

        let sw = new StreamWriter("./main.go")
        writeBlocks sw blocks consts
        sw.Flush()

        Environment.CurrentDirectory <- "./output"
        Console.WriteLine("Switched directory {0}", Environment.CurrentDirectory)

        let exeRes = Shell.executeShellCommand "make MODE=debug" |> Async.RunSynchronously
        if exeRes.ExitCode <> 0
        then
            eprintfn "%s" exeRes.StandardError
            Environment.Exit 1
        else printfn "%s" exeRes.StandardOutput
        Console.WriteLine("application build successful")

        let runRes = Shell.executeShellCommand "./build/debug/mochivm" |> Async.RunSynchronously
        if runRes.ExitCode = 0
        then
            printfn "%s" runRes.StandardOutput
            printfn "App ran successfully"
        else
            printfn "%s" runRes.StandardError
            printfn "App run failed"
        runRes.ExitCode