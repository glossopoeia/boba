namespace Mochi.Simulator

open System;

open Mochi.Core.Instructions
open Mochi.Simulator.Machine

module Evaluation =

    let setAt index elem ls = ls |> List.mapi (fun k v -> if k = index then elem else v)

    let getCaptured machine closed = List.map (fun (frame, ind) -> getFrameValue machine frame ind) closed

    let pushValue value machine = { machine with Stack = value :: machine.Stack; CodePointer = next machine }

    let popPushValue value machine = { machine with Stack = value :: machine.Stack.Tail; CodePointer = next machine }

    let popPopPushValue value machine = { machine with Stack = value :: machine.Stack.Tail.Tail; CodePointer = next machine }

    let topTwo machine = (machine.Stack.Head, machine.Stack.Tail.Head)

    /// Executes the given instruction on the given machine state. 
    let step instruction machine =
        Console.Write(instruction.ToString() + ": ")
        Console.WriteLine(machine.Stack)
        match instruction with
        | INop -> { machine with CodePointer = next machine }
        | IAbort 0 -> { machine with CodePointer = machine.Code.Instructions.Length }

        | IOffset i -> { machine with CodePointer = machine.CodePointer - i }
        | IReturn ->
            let (FFunFrame (_, retPtr)) = machine.Frames.Head
            { machine with Frames = machine.Frames.Tail; CodePointer = retPtr }
        | ICall target ->
            { machine with Frames = FFunFrame ([], next machine) :: machine.Frames; CodePointer = getIndex target machine }
        | ITailCall target -> { machine with CodePointer = getIndex target machine }
        | IStore count ->
            { machine with
                Stack = List.skip count machine.Stack;
                Frames = FVarFrame (List.take count machine.Stack) :: machine.Frames;
                CodePointer = next machine }
        | IOverwrite (frame, index) ->
            let (FFunFrame (oldFrame, oldPtr)) = machine.Frames.Item frame
            let newFrame = FFunFrame (setAt index (oldFrame.Item index) oldFrame, oldPtr)
            { machine with
                Stack = machine.Stack.Tail;
                Frames = newFrame :: machine.Frames.Tail;
                CodePointer = next machine }
        | IForget -> { machine with Frames = machine.Frames.Tail; CodePointer = next machine }
        | IFind (frame, index) -> { machine with Stack = getFrameValue machine frame index :: machine.Stack; CodePointer = next machine }
        | ICallClosure ->
            let (VClosure (body, args, captured)) = machine.Stack.Head
            let cap = List.append (List.take args machine.Stack.Tail) captured.Value
            { machine with
                Stack = List.skip args machine.Stack.Tail;
                Frames = FFunFrame (cap, next machine) :: machine.Frames;
                CodePointer = body }
        | ITailCallClosure ->
            let (VClosure (body, args, captured)) = machine.Stack.Head
            let (FFunFrame (_, retPtr)) = machine.Frames.Head
            let cap = List.append (List.take args machine.Stack.Tail) captured.Value
            { machine with
                Stack = List.skip args machine.Stack.Tail;
                Frames = FFunFrame (cap, retPtr) :: machine.Frames.Tail;
                CodePointer = body }
        | IClosure (body, args, closed) ->
            { machine with
                Stack = VClosure (getIndex body machine, args, ref (getCaptured machine closed)) :: machine.Stack;
                CodePointer = next machine }
        | IRecursive (body, args, closed) ->
            let captured = ref (getCaptured machine closed)
            let closure = VClosure (getIndex body machine, args, captured)
            captured.Value <- closure :: captured.Value
            { machine with Stack = closure :: machine.Stack; CodePointer = next machine }
        | IMutual nrec ->
            let closures = List.take nrec machine.Stack
            let captured = List.map (fun c -> let (VClosure (cb, ca, cc)) = c in cc) closures
            for c in captured do
                c.Value <- List.append closures c.Value
            { machine with CodePointer = next machine }

        | IHandle (handleId, after, args, opCount) ->
            let ops = List.take opCount machine.Stack
            let belowOps = List.skip opCount machine.Stack
            let retClosure = belowOps.Head
            let argValues = List.take args belowOps.Tail
            let newStack = List.skip args belowOps.Tail
            { machine with
                Stack = newStack;
                Frames = FMarkFrame (handleId, argValues, retClosure, ops, after + machine.CodePointer) :: machine.Frames;
                CodePointer = next machine }
        | IComplete ->
            let (FMarkFrame (handleId, args, VClosure (retBody, cargs, retClosed), ops, afterPtr)) = machine.Frames.Head
            let cap = List.append (List.take cargs machine.Stack) retClosed.Value
            { machine with
                Stack = List.skip cargs machine.Stack
                Frames = FFunFrame (List.append args cap, afterPtr) :: machine.Frames.Tail;
                CodePointer = retBody }
        | IEscape (handleId, opId) ->
            let (FMarkFrame (id, handleArgs, _, ops, after)) = findNestedHandlerWithId handleId machine.Frames
            let (VClosure (body, opArgs, closed)) = ops.[opId]
            let cont = VContinuation (next machine, handleArgs.Length, getFramesToNestedHandler handleId machine.Frames, List.skip opArgs machine.Stack)
            let opEnv = cont :: List.append (List.take opArgs machine.Stack) (List.append handleArgs !closed)
            { machine with
                Stack = List.empty;
                Frames = FFunFrame (opEnv, after) :: dropFramesToNestedHandler handleId machine.Frames;
                CodePointer = body }
        | ICallContinuation ->
            let (VContinuation (resume, contArgs, capturedFrames, capturedStack)) = machine.Stack.Head
            let (FMarkFrame (handleId, handleArgs, retClosure, ops, after)) = List.last capturedFrames
            let args = List.take contArgs machine.Stack.Tail
            let newHandler = FMarkFrame (handleId, args, retClosure, ops, next machine)
            { machine with
                Stack = List.append (List.skip (contArgs + 1) machine.Stack) capturedStack;
                Frames = List.append (List.take (capturedFrames.Length - 1) capturedFrames) (newHandler :: machine.Frames);
                CodePointer = resume }
        | ITailCallContinuation ->
            let (VContinuation (resume, contArgs, capturedFrames, capturedStack)) = machine.Stack.Head
            let (FFunFrame (env, retPtr)) = machine.Frames.Head
            let (FMarkFrame (handleId, handleArgs, retClosure, ops, after)) = List.last capturedFrames
            let args = List.take contArgs machine.Stack.Tail
            let newHandler = FMarkFrame (handleId, args, retClosure, ops, retPtr)
            { machine with
                Stack = List.append (List.skip (contArgs + 1) machine.Stack) capturedStack;
                Frames = List.append (List.take (capturedFrames.Length - 1) capturedFrames) (newHandler :: machine.Frames.Tail);
                CodePointer = resume }

        | IShuffle (count, indices) ->
            let items = List.take count machine.Stack
            let newStack = List.append (List.map (fun i -> items.[i]) indices) (List.skip count machine.Stack)
            { machine with Stack = newStack; CodePointer = next machine }

        | IJumpIf target ->
            let (VBool top) = machine.Stack.Head
            { machine with
                Stack = machine.Stack.Tail;
                CodePointer = if top then getIndex target machine else next machine; }
        | IJumpIfNot target ->
            let (VBool top) = machine.Stack.Head
            { machine with
                Stack = machine.Stack.Tail;
                CodePointer = if not top then getIndex target machine else next machine; }
        | IJumpStruct (ctorId, target) ->
            let (VConstructed (valCtor, _)) = machine.Stack.Head
            { machine with CodePointer = if ctorId = valCtor then getIndex target machine else next machine }
        
        | IOffsetIf target ->
            let (VBool top) = machine.Stack.Head
            { machine with
                Stack = machine.Stack.Tail;
                CodePointer = if top then machine.CodePointer + target else next machine; }
        | IOffsetIfNot target ->
            let (VBool top) = machine.Stack.Head
            { machine with
                Stack = machine.Stack.Tail;
                CodePointer = if not top then machine.CodePointer + target else next machine; }
        | IOffsetStruct (ctorId, target) ->
            let (VConstructed (valCtor, _)) = machine.Stack.Head
            { machine with CodePointer = if ctorId = valCtor then machine.CodePointer + target else next machine }

        | INewRef ->
            let id = Guid.NewGuid ()
            { machine with
                Stack = VRef id :: machine.Stack.Tail;
                Heap = Map.add id machine.Stack.Head machine.Heap;
                CodePointer = next machine }
        | IGetRef ->
            let (VRef id) = machine.Stack.Head
            { machine with
                Stack = machine.Heap.[id] :: machine.Stack.Tail;
                CodePointer = next machine }
        | IPutRef ->
            let (VRef id) = machine.Stack.Tail.Head
            { machine with
                Stack = machine.Stack.Tail;
                Heap = Map.add id machine.Stack.Head machine.Heap;
                CodePointer = next machine }

        | IConstruct (ctorId, itemCount) ->
            { machine with
                Stack = VConstructed (ctorId, List.take itemCount machine.Stack) :: List.skip itemCount machine.Stack;
                CodePointer = next machine }
        | IDestruct ->
            let (VConstructed (_, vals)) = machine.Stack.Head
            { machine with Stack = List.append vals machine.Stack.Tail; CodePointer = next machine }
        | IIsStruct ctorId ->
            let (VConstructed (valId, _)) = machine.Stack.Head
            { machine with Stack = VBool (valId = ctorId) :: machine.Stack; CodePointer = next machine }

        | IEmptyRecord -> pushValue (VRecord Map.empty) machine

        | IListNil -> pushValue (VList List.empty) machine
        | IListCons ->
            let (VList ls) = machine.Stack.Tail.Head
            popPopPushValue (VList (machine.Stack.Head :: ls)) machine
        | IListHead ->
            let (VList ls) = machine.Stack.Head
            popPushValue ls.Head machine
        | IListTail ->
            let (VList ls) = machine.Stack.Head
            popPushValue (VList ls.Tail) machine
        | IListAppend ->
            let (VList ls) = machine.Stack.Head
            let (VList rs) = machine.Stack.Tail.Head
            popPopPushValue (VList (List.append ls rs)) machine

        | ITrue -> pushValue (VBool true) machine
        | IFalse -> pushValue (VBool false) machine
        | IBoolNot ->
            let (VBool n) = machine.Stack.Head
            popPushValue (VBool (not n)) machine
        | IBoolAnd ->
            let (VBool l, VBool r) = topTwo machine
            popPopPushValue (VBool (l && r)) machine
        | IBoolOr ->
            let (VBool l, VBool r) = topTwo machine
            popPopPushValue (VBool (l || r)) machine
        | IBoolXor ->
            let (VBool l, VBool r) = topTwo machine
            popPopPushValue (VBool (l <> r)) machine
        | IBoolEq ->
            let (VBool l, VBool r) = topTwo machine
            popPopPushValue (VBool (l = r)) machine

        | II8 lit -> pushValue (VInt8 lit) machine
        | IU8 lit -> pushValue (VUInt8 lit) machine
        | II16 lit -> pushValue (VInt16 lit) machine
        | IU16 lit -> pushValue (VUInt16 lit) machine
        | II32 lit -> pushValue (VInt32 lit) machine
        | IU32 lit -> pushValue (VUInt32 lit) machine
        | II64 lit -> pushValue (VInt64 lit) machine
        | IU64 lit -> pushValue (VUInt64 lit) machine
        | IISize lit -> pushValue (VISize lit) machine
        | IUSize lit -> pushValue (VUSize lit) machine
        | ISingle lit -> pushValue (VSingle lit) machine
        | IDouble lit -> pushValue (VDouble lit) machine

        | IIntAdd s ->
            match s with
            | I8 -> let VInt8 l :: VInt8 r :: _ = machine.Stack in popPopPushValue (VInt8 (l + r)) machine
            | U8 -> let VUInt8 l :: VUInt8 r :: _ = machine.Stack in popPopPushValue (VUInt8 (l + r)) machine
            | I16 -> let VInt16 l :: VInt16 r :: _ = machine.Stack in popPopPushValue (VInt16 (l + r)) machine
            | U16 -> let VUInt16 l :: VUInt16 r :: _ = machine.Stack in popPopPushValue (VUInt16 (l + r)) machine
            | I32 -> let VInt32 l :: VInt32 r :: _ = machine.Stack in popPopPushValue (VInt32 (l + r)) machine
            | U32 -> let VUInt32 l :: VUInt32 r :: _ = machine.Stack in popPopPushValue (VUInt32 (l + r)) machine
            | I64 -> let VInt64 l :: VInt64 r :: _ = machine.Stack in popPopPushValue (VInt64 (l + r)) machine
            | U64 -> let VUInt64 l :: VUInt64 r :: _ = machine.Stack in popPopPushValue (VUInt64 (l + r)) machine
            | ISize -> let VISize l :: VISize r :: _ = machine.Stack in popPopPushValue (VISize (l + r)) machine
            | USize -> let VUSize l :: VUSize r :: _ = machine.Stack in popPopPushValue (VUSize (l + r)) machine
        | IIntAddOvf s -> failwith "Not yet implemented; for ease of implementation in F# this needs to be in a separate function with a checked context."
        | IIntSub s ->
            match s with
            | I8 -> let VInt8 l :: VInt8 r :: _ = machine.Stack in popPopPushValue (VInt8 (l - r)) machine
            | U8 -> let VUInt8 l :: VUInt8 r :: _ = machine.Stack in popPopPushValue (VUInt8 (l - r)) machine
            | I16 -> let VInt16 l :: VInt16 r :: _ = machine.Stack in popPopPushValue (VInt16 (l - r)) machine
            | U16 -> let VUInt16 l :: VUInt16 r :: _ = machine.Stack in popPopPushValue (VUInt16 (l - r)) machine
            | I32 -> let VInt32 l :: VInt32 r :: _ = machine.Stack in popPopPushValue (VInt32 (l - r)) machine
            | U32 -> let VUInt32 l :: VUInt32 r :: _ = machine.Stack in popPopPushValue (VUInt32 (l - r)) machine
            | I64 -> let VInt64 l :: VInt64 r :: _ = machine.Stack in popPopPushValue (VInt64 (l - r)) machine
            | U64 -> let VUInt64 l :: VUInt64 r :: _ = machine.Stack in popPopPushValue (VUInt64 (l - r)) machine
            | ISize -> let VISize l :: VISize r :: _ = machine.Stack in popPopPushValue (VISize (l - r)) machine
            | USize -> let VUSize l :: VUSize r :: _ = machine.Stack in popPopPushValue (VUSize (l - r)) machine
        | IIntSubOvf s -> failwith "Not yet implemented; for ease of implementation in F# this needs to be in a separate function with a checked context."
        | IIntMul s ->
            match s with
            | I8 -> let VInt8 l :: VInt8 r :: _ = machine.Stack in popPopPushValue (VInt8 (l * r)) machine
            | U8 -> let VUInt8 l :: VUInt8 r :: _ = machine.Stack in popPopPushValue (VUInt8 (l * r)) machine
            | I16 -> let VInt16 l :: VInt16 r :: _ = machine.Stack in popPopPushValue (VInt16 (l * r)) machine
            | U16 -> let VUInt16 l :: VUInt16 r :: _ = machine.Stack in popPopPushValue (VUInt16 (l * r)) machine
            | I32 -> let VInt32 l :: VInt32 r :: _ = machine.Stack in popPopPushValue (VInt32 (l * r)) machine
            | U32 -> let VUInt32 l :: VUInt32 r :: _ = machine.Stack in popPopPushValue (VUInt32 (l * r)) machine
            | I64 -> let VInt64 l :: VInt64 r :: _ = machine.Stack in popPopPushValue (VInt64 (l * r)) machine
            | U64 -> let VUInt64 l :: VUInt64 r :: _ = machine.Stack in popPopPushValue (VUInt64 (l * r)) machine
            | ISize -> let VISize l :: VISize r :: _ = machine.Stack in popPopPushValue (VISize (l * r)) machine
            | USize -> let VUSize l :: VUSize r :: _ = machine.Stack in popPopPushValue (VUSize (l * r)) machine
        | IIntMulOvf s -> failwith "Not yet implemented; for ease of implementation in F# this needs to be in a separate function with a checked context."

    let rec run machine =
        if machine.CodePointer < machine.Code.Instructions.Length
        then run (step (machine.Code.Instructions.Item machine.CodePointer) machine)
        else machine