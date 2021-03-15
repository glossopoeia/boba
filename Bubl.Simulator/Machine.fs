namespace Bubl.Simulator

open System;

open Bubl.Core.Instructions;

module Machine =

    type Value =
        | VBool of bool
        | VInt8 of sbyte
        | VUInt8 of byte
        | VInt16 of int16
        | VUInt16 of uint16
        | VInt32 of int32
        | VUInt32 of uint32
        | VInt64 of int64
        | VUInt64 of uint64
        | VISize of int
        | VUSize of uint
        | VHalf of System.Half
        | VSingle of single
        | VDouble of double
        | VRef of Guid
        | VList of List<Value>
        | VClosure of body: int * captured: ref<List<Value>>
        | VOperationClosure of body: int * args: int * captured: List<Value>
        | VContinuation of resumePtr: int * args: int * capturedFrames: List<Frame> * capturedStack: List<Value>
        | VConstructed of ctorId: int * args: List<Value>
    and Frame =
        | FVarFrame of List<Value>
        | FFunFrame of List<Value> * retPtr: int
        | FMarkFrame of List<Value> * retClosure: Value * opClosures: Map<string, Value> * after: int

    let frameHasOperation operation frame =
        match frame with
        | FMarkFrame (_, _, ops, _) -> Map.containsKey operation ops
        | _ -> false

    let findHandlerWithOperation operation fs = List.find (frameHasOperation operation) fs

    let getFramesToHandler operation fs = List.take (List.findIndex (frameHasOperation operation) fs + 1) fs

    let dropFramesToHandler operation fs = List.skip (List.findIndex (frameHasOperation operation) fs + 1) fs

    type Program = { Labels: Map<string, int>; Instructions: List<Instruction> }

    type Machine = {
        Stack: List<Value>;
        Frames: List<Frame>;
        Heap: Map<Guid, Value>;
        Code: Program;
        CodePointer: int
    }

    let getFrameValue machine frame index =
        match machine.Frames.Item frame with
        | FVarFrame ls -> ls.Item index
        | FFunFrame (ls, _) -> ls.Item index
        | FMarkFrame (ls, _, _, _) -> ls.Item index

    let getIndex target machine =
        match target with
        | Label s -> machine.Code.Labels.Item s
        | Index i -> i

    let next machine = machine.CodePointer + 1

    let blocksToProgram blocks =
        let lengths = List.map blockLength blocks
        let (startIndices, endInd) = List.mapFold (fun indAcc len -> indAcc, indAcc + len) 0 lengths
        let labelPointers =
            List.fold2
                (fun ptrs block ind ->
                    match block with
                    | BLabeled (label, _) -> Map.add label ind ptrs
                    | _ -> ptrs)
                Map.empty blocks startIndices
        { Labels = labelPointers; Instructions = List.map blockInstructions blocks |> List.concat }

    let newMachine blocks = {
            Stack = List.empty;
            Frames = List.empty;
            Heap = Map.empty;
            Code = blocksToProgram blocks;
            CodePointer = 0
        }