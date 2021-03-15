namespace Bubl.Simulator

open System;

open Bubl.Core.Instructions
open Bubl.Simulator.Machine

module Evaluation =

    let setAt index elem ls = ls |> List.mapi (fun k v -> if k = index then elem else v)

    let getCaptured machine closed = List.map (fun (frame, ind) -> getFrameValue machine frame ind) closed

    let pushValue value machine = { machine with Stack = value :: machine.Stack; CodePointer = next machine }

    let pushPopValue value machine = { machine with Stack = value :: machine.Stack.Tail; CodePointer = next machine }

    let step instruction machine =
        match instruction with
        | INop -> { machine with CodePointer = next machine }

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
            let (VClosure (body, captured)) = machine.Stack.Head
            { machine with
                Stack = machine.Stack.Tail;
                Frames = FFunFrame (!captured, next machine) :: machine.Frames;
                CodePointer = body }
        | ITailCallClosure ->
            let (VClosure (body, captured)) = machine.Stack.Head
            let (FFunFrame (_, retPtr)) = machine.Frames.Head
            { machine with
                Stack = machine.Stack.Tail;
                Frames = FFunFrame (!captured, retPtr) :: machine.Frames.Tail;
                CodePointer = body }
        | IClosure (body, closed) ->
            { machine with
                Stack = VClosure (body, ref (getCaptured machine closed)) :: machine.Stack;
                CodePointer = next machine }
        | IRecursive (body, closed) ->
            let captured = ref (getCaptured machine closed)
            let closure = VClosure (body, captured)
            captured := closure :: !captured
            { machine with Stack = closure :: machine.Stack; CodePointer = next machine }
        | IMutual nrec ->
            let closures = List.take nrec machine.Stack
            let captured = List.map (fun c -> let (VClosure (cb, cc)) = c in cc) closures
            for c in captured do
                c := List.append closures !c
            { machine with CodePointer = next machine }

        | IOperationClosure (body, args, closed) ->
            { machine with
                Stack = VOperationClosure (body, args, getCaptured machine closed) :: machine.Stack;
                CodePointer = next machine }
        | IHandle (after, args, opIds) ->
            let ops = List.zip opIds (List.take opIds.Length machine.Stack) |> Map.ofList
            let belowOps = List.skip opIds.Length machine.Stack
            let retClosure = belowOps.Head
            let argValues = List.take args belowOps.Tail
            let newStack = List.skip args belowOps.Tail
            { machine with
                Stack = newStack;
                Frames = FMarkFrame (argValues, retClosure, ops, after + machine.CodePointer) :: machine.Frames;
                CodePointer = next machine }
        | IComplete ->
            let (FMarkFrame (args, VClosure (retBody, retClosed), ops, afterPtr)) = machine.Frames.Head
            { machine with
                Frames = FFunFrame (List.append args !retClosed, afterPtr) :: machine.Frames.Tail;
                CodePointer = retBody }
        | IEscape operation ->
            let (FMarkFrame (handleArgs, _, ops, after)) = findHandlerWithOperation operation machine.Frames
            let (VOperationClosure (body, opArgs, closed)) = ops.[operation]
            let opEnv = List.append (List.take opArgs machine.Stack) (List.append handleArgs closed)
            { machine with
                Stack = List.empty;
                Frames = FFunFrame (opEnv, after) :: dropFramesToHandler operation machine.Frames;
                CodePointer = body }
        | IOperation operation ->
            let (FMarkFrame (handleArgs, _, ops, after)) = findHandlerWithOperation operation machine.Frames
            let (VOperationClosure (body, opArgs, closed)) = ops.[operation]
            let cont = VContinuation (next machine, handleArgs.Length, getFramesToHandler operation machine.Frames, List.skip opArgs machine.Stack)
            let opEnv = cont :: List.append (List.take opArgs machine.Stack) (List.append handleArgs closed)
            { machine with
                Stack = List.empty;
                Frames = FFunFrame (opEnv, after) :: dropFramesToHandler operation machine.Frames;
                CodePointer = body }
        | ICallContinuation ->
            let (VContinuation (resume, contArgs, capturedFrames, capturedStack)) = machine.Stack.Head
            let (FMarkFrame (handleArgs, retClosure, ops, after)) = List.last capturedFrames
            let args = List.take contArgs machine.Stack.Tail
            let newHandler = FMarkFrame (args, retClosure, ops, next machine)
            { machine with
                Stack = List.append (List.skip (contArgs + 1) machine.Stack) capturedStack;
                Frames = List.append (List.take (capturedFrames.Length - 1) capturedFrames) (newHandler :: machine.Frames);
                CodePointer = resume }
        | ITailCallContinuation ->
            let (VContinuation (resume, contArgs, capturedFrames, capturedStack)) = machine.Stack.Head
            let (FFunFrame (env, retPtr)) = machine.Frames.Head
            let (FMarkFrame (handleArgs, retClosure, ops, after)) = List.last capturedFrames
            let args = List.take contArgs machine.Stack.Tail
            let newHandler = FMarkFrame (args, retClosure, ops, retPtr)
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

        | IListNil -> pushValue (VList List.empty) machine
        | IListCons ->
            let (VList ls) = machine.Stack.Tail.Head
            { machine with Stack = VList (machine.Stack.Head :: ls) :: machine.Stack.Tail.Tail; CodePointer = next machine }
        | IListSnoc ->
            let (VList ls) = machine.Stack.Tail.Head
            { machine with Stack = VList (List.append ls [machine.Stack.Head]) :: machine.Stack.Tail.Tail; CodePointer = next machine }
        | IListHead ->
            let (VList ls) = machine.Stack.Head
            pushPopValue ls.Head machine
        | IListLast ->
            let (VList ls) = machine.Stack.Head
            pushPopValue (List.last ls) machine
        | IListTail ->
            let (VList ls) = machine.Stack.Head
            pushPopValue (VList ls.Tail) machine
        | IListInit ->
            let (VList ls) = machine.Stack.Head
            pushPopValue (VList (List.take (ls.Length - 1) ls)) machine
        | IListAppend ->
            let (VList ls) = machine.Stack.Head
            let (VList rs) = machine.Stack.Tail.Head
            { machine with Stack = (VList (List.append ls rs)) :: machine.Stack; CodePointer = next machine }
        | IListIsEmpty ->
            let (VList ls) = machine.Stack.Head
            pushValue (VBool ls.IsEmpty) machine

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
        | IHalf lit -> pushValue (VHalf lit) machine
        | ISingle lit -> pushValue (VSingle lit) machine
        | IDouble lit -> pushValue (VDouble lit) machine


    let rec run machine =
        if machine.CodePointer < machine.Code.Instructions.Length
        then run (step (machine.Code.Instructions.Item machine.CodePointer) machine)
        else machine