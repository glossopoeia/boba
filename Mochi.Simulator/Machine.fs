namespace Mochi.Simulator

open System;

open Mochi.Core.Instructions;

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
        | VSingle of single
        | VDouble of double
        /// A reference value contains a 'pointer' into the heap. The basic operations on a reference value allow
        /// programmers to retrieve or update the 'pointed' value within the heap. But the reference value itself
        /// does not contain the actual value.
        | VRef of Guid
        | VList of List<Value>
        | VClosure of body: int * args: int * captured: ref<List<Value>>
        | VContinuation of resumePtr: int * args: int * capturedFrames: List<Frame> * capturedStack: List<Value>
        | VConstructed of ctorId: int * args: List<Value>
        | VRecord of Map<int, Value>
    and Frame =
        | FVarFrame of List<Value>
        | FFunFrame of List<Value> * retPtr: int
        | FMarkFrame of handleId: int * List<Value> * retClosure: Value * opClosures: List<Value> * after: int

    let frameHasHandleId handleId frame =
        match frame with
        | FMarkFrame (id, _, _, _, _) -> handleId = id
        | _ -> false

    let findNestedHandlerWithId handleId fs = List.find (frameHasHandleId handleId) fs

    let getFramesToNestedHandler handleId fs = List.take (List.findIndex (frameHasHandleId handleId) fs + 1) fs

    let dropFramesToNestedHandler handleId fs = List.skip (List.findIndex (frameHasHandleId handleId) fs + 1) fs

    type Machine = {
        Stack: List<Value>;
        Frames: List<Frame>;
        Heap: Map<Guid, Value>;
        Code: LabeledBytecode;
        CodePointer: int
    }

    let getFrameValue machine frame index =
        match machine.Frames.Item frame with
        | FVarFrame ls -> ls.Item index
        | FFunFrame (ls, _) -> ls.Item index
        | FMarkFrame (_, ls, _, _, _) -> ls.Item index

    let getIndex target machine =
        match target with
        | Label s -> machine.Code.Labels.Item s
        | Index i -> i

    let next machine = machine.CodePointer + 1

    let newMachine blocks = {
            Stack = List.empty;
            Frames = List.empty;
            Heap = Map.empty;
            Code = delabel blocks;
            CodePointer = 0
        }