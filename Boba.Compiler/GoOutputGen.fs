namespace Boba.Compiler

module GoOutputGen =

    open System
    open System.IO
    open Boba.Compiler.CoreGen
    open Mochi.Core.Instructions

    let permissions =
        Map.empty
        |> Map.add "console" 0
        |> Map.add "network" 1

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
    
    let getPermissionBytes (perms: Map<string, int>) target =
        match target with
        | Label s -> perms.[s].ToString()
        | Index i -> int(i).ToString()

    let writeInstruction stream labels natives instr =
        match instr with
        | INop -> ()
        //| INop -> writeByte stream "runtime.NOP"
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
        | IOverwrite ind ->
            writeByte stream "runtime.OVERWRITE"
            writeUInt stream ind
        | IForget amt ->
            writeByte stream "runtime.FORGET"
            writeByte stream amt
        | IFind (ind) ->
            writeByte stream "runtime.FIND"
            writeUInt stream ind
        | ICallClosure -> writeByte stream "runtime.CALL_CLOSURE"
        | ITailCallClosure -> writeByte stream "runtime.TAILCALL_CLOSURE"
        | IClosure (body, args, closed) ->
            writeByte stream "runtime.CLOSURE"
            writeUInt stream (getLocationBytes labels body)
            writeByte stream args
            writeUShort stream closed.Length
            closed |> Seq.iter (fun i -> writeUInt stream i)
        | IRecursive (body, args, closed) ->
            writeByte stream "runtime.RECURSIVE"
            writeUInt stream body
            writeByte stream args
            writeUShort stream closed.Length
            closed |> Seq.iter (fun i -> writeUInt stream i)
        | IMutual n ->
            writeByte stream "runtime.MUTUAL"
            writeByte stream n
        | ICallNative loc ->
            writeByte stream "runtime.CALL_NATIVE"
            writeUInt stream (getLocationBytes natives loc)
        | IHasPermission loc ->
            writeByte stream "runtime.HAS_PERMISSION"
            writeUInt stream (getPermissionBytes permissions loc)
        | IRequestPermission loc ->
            writeByte stream "runtime.REQUEST_PERMISSION"
            writeInt stream (getPermissionBytes permissions loc)
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
        | IRecordSelect l ->
            writeByte stream "runtime.RECORD_SELECT"
            writeInt stream l
        
        | IVariant l ->
            writeByte stream "runtime.VARIANT"
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
        
        | IConstruct (id, argCount) ->
            writeByte stream "runtime.CONSTRUCT"
            writeInt stream id
            writeByte stream argCount
        | IDestruct -> writeByte stream "runtime.DESTRUCT"
        | IIsStruct id ->
            writeByte stream "runtime.IS_COMPOSITE"
            writeInt stream id
        
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

        | IPrint -> writeByte stream "runtime.PRINT"

        | IStringPlaceholder _ -> failwith "Bytecode generation encountered a placeholder that should have been removed."

    let writeLabel (stream: StreamWriter) labelIdx labelText =
        stream.WriteLine("    vm.AddLabel(\"" + labelText + "\", " + labelIdx.ToString() + ")")

    let writeConstant (stream: StreamWriter) constant =
        match constant with
        | IStringPlaceholder s ->
            stream.WriteLine("    vm.AddConstant(" + s + ")")
        | _ -> failwith "Tried to write a non-constant as a constant."

    let writeConstants stream consts =
        consts |> Seq.iter (writeConstant stream)

    let cleanseNativeName (name: string) = name.Replace("-", "_").Replace(".", "_")
    
    let stripCodeLine (natCodeLine: Syntax.NativeCodeLine) =
        natCodeLine.Line.[1..].Trim()

    let writeNative (sw: StreamWriter) name codes =
        sw.WriteLine($"func {cleanseNativeName name}(machine *runtime.Machine, fiber *runtime.Fiber) {{")
        for line in codes do
            sw.WriteLine($"\t" + stripCodeLine line)
        sw.WriteLine("}")
        sw.WriteLine("")
    
    let writeNatives natives =
        for n in natives do
            let sw = new StreamWriter($"./{n.UnitName}.go")
            sw.WriteLine("package main")
            sw.WriteLine("")
            sw.WriteLine("import (")
            for path in n.Imports do
                sw.WriteLine($"    " + path.ToString())
            if not (Map.isEmpty n.Decls)
            then sw.WriteLine("    \"github.com/glossopoeia/boba/runtime\"")
            sw.WriteLine(")")
            sw.WriteLine("")
            Map.iter (fun name nat -> writeNative sw name nat) n.Decls
            sw.Flush()
            sw.Close()

    let writeNativeInject (stream: StreamWriter) name =
        stream.WriteLine($"    vm.RegisterNative(\"{name}\", {cleanseNativeName name})")
    
    let writeNativeInjects stream names =
        // write the native function registrations in order of their id
        let names = Map.toSeq names |> Seq.sortBy snd |> Seq.map fst
        for n in names do
            writeNativeInject stream n

    let writeBytecode stream (bytecode: LabeledBytecode) nativeMap =
        bytecode.Instructions |> Seq.iter (writeInstruction stream bytecode.Labels nativeMap)
        bytecode.Labels |> Seq.iter (fun l -> writeLabel stream l.Value l.Key)

    let writeBlocks stream consts (mapped: LabeledBytecode) nativeMap =
        writeHeader stream
        writeConstants stream consts
        writeNativeInjects stream nativeMap
        writeBytecode stream mapped nativeMap
        writeFooter stream

    let writeAndRunDebug natives blocks consts =
        let mapped = delabelBytes blocks
        let nativeMap =
            List.concat [for n in natives -> [for d in n.Decls -> $"{d.Key}"]]
            |> List.mapi (fun i n -> (n, i))
            |> Map.ofList
        writeNatives natives
        let sw = new StreamWriter("./main.go")
        writeBlocks sw consts mapped nativeMap
        sw.Flush()
        sw.Close()

        let runRes = Shell.executeCommand "go" ["run"; "."] |> Async.RunSynchronously
        if runRes.ExitCode = 0
        then
            printfn "%s" runRes.StandardOutput
            printfn "App ran successfully"
        else
            printfn "%s" runRes.StandardError
            printfn "App run failed"
        runRes.ExitCode