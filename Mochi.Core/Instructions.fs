namespace Mochi.Core

module Instructions =

    type JumpTarget =
        | Label of string
        | Index of int

    type Instruction =
        /// No op, doesn't do anything, moves on to the next instruction
        | INop
        /// Placeholder for breakpoints when debugging.
        | IBreakpoint
        /// Terminate the current fiber.
        | IAbort
        /// Given an index into the constant pool, place the value at that index on top of the stack.
        | IConstant of poolIndex: uint16

        /// Moves the instruction pointer forward by the specified amount.
        | IOffset of relative: int
        /// Sets the instruction pointer to the 'return instruction pointer' in the function frame on top of
        /// the frame stack. Pops the top of the frame stack.
        | IReturn
        /// Sets the instruction pointer to the target and pushes a new function frame. Expects the code block
        /// at the target to end with a return instruction.
        | ICall of target: JumpTarget
        /// Sets the instruction pointer to the target without pushing a new function frame. Expects the code block
        /// at the target to end with a return instruction. Equivalen to just jumping to the target location.
        | ITailCall of target: JumpTarget
        /// Create a new frame containing the top N values from the stack. Then pop N values off the stack.
        | IStore of count: int
        /// Overwrite the value at the index in the Nth frame from the top of the frame stack with the value
        /// at the top of the value stack. Then pop the top of the value stack.
        | IOverwrite of index: int
        /// Pop the top of the frame stack.
        | IForget of count: int
        /// Get the value stored in the given frame at the given index and put it on top of the stack.
        | IFind of index: int
        /// Pop the closure value on top of the stack. Push a new function frame with the values captured by
        /// the closure and set the return pointer to be the next instruction. Then jump to the instruction
        /// pointed to by the closure body.
        | ICallClosure
        /// Pop the closure value on top of the stack, and pop the top function frame. Push a new function
        /// frame with the values captured by the closure and the retur pointer stored in the previous top
        /// function frame. Then jump to the instruction pointed to by the closure body. Note that the replacement
        /// semantics for the return value imply that tail-calls cannot be performed at the top level of a program
        /// or within the scope of variable/mark-frames. Those scopes should use ICallClosure so that they get
        /// cleaned up properly.
        | ITailCallClosure
        /// Push a closure for the given pointer to a function body, storing references to the values in the frame
        /// stack referenced by the list of values to 'close' over. Also signify how many stack values will be taken
        /// directly off the stack at the call-site and stored into the closure frame.
        | IClosure of body: JumpTarget * args: int * closed: List<int>
        /// Push a recursive closure for the given pointer to a function body, storing references to the values in the frame
        /// stack referenced by the list of values to 'close' over. The reference to the closure itself is stored at index 0
        /// of the closed values list.
        | IRecursive of body: JumpTarget * args: int * closed: List<int>
        /// Given a list of n closures on top of the stack, make them all mutually recursive with respect to each other by
        /// inserting references to each other into their stored closed values. The layout of references is the same for each
        /// closure environment: closure at the top of the stack becomes item 0 in the closed list, closure one down from the
        /// top becomes item 1 in the closed list, etc.
        | IMutual of count: int

        | ICallNative of nat: JumpTarget
        | IRequestPermission of perm: JumpTarget
        | IHasPermission of perm: JumpTarget

        | INewNursery
        | IWaitNursery
        | IPushCancel
        | IPopContext

        | IHandle of handleId: int * after: int * args: int * operations: int
        | IInject of handleId: int
        | IEject of handleId: int
        | IComplete
        | IEscape of handleId: int * opId: int
        | ICallContinuation
        | ITailCallContinuation

        | IShuffle of count: int * indices: List<int>

        | IJumpIf of target: JumpTarget
        | IJumpIfNot of target: JumpTarget
        | IJumpStruct of ctorId: int * target: JumpTarget
        | IJumpPermission of perm: JumpTarget * target: JumpTarget
        
        | IOffsetIf of relative: int
        | IOffsetIfNot of relative: int
        | IOffsetStruct of ctorId: int * relative: int
        | IOffsetPermission of permId: int * relative: int

        | IConstruct of ctorId: int * args: int
        | IDestruct
        | IIsStruct of ctorId: int

        | IEmptyRecord
        | IRecordExtend of int
        | IRecordSelect of int

        | IVariant of label: int
        | IIsCase of label: int
        | IJumpCase of label: int * target: JumpTarget
        | IOffsetCase of label: int * relative: int

        | II8 of value: sbyte
        | IU8 of value: byte
        | II16 of value: int16
        | IU16 of value: uint16
        | II32 of value: int32
        | IU32 of value: uint32
        | II64 of value: int64
        | IU64 of value: uint64
        | IINative of value: nativeint
        | IUNative of value: unativeint
        | ISingle of value: single
        | IDouble of value: double
        | IRune of value: char

        | IStringPlaceholder of string

    type Block =
        | BUnlabeled of List<Instruction>
        | BLabeled of string * List<Instruction>

    type LabeledBytecode =
        { Labels: Map<string, int>;
          Instructions: List<Instruction> }

    let instructionByteLength instr =
        match instr with
        | IAbort _ -> 2
        | IConstant _ -> 3
        | IStringPlaceholder _ -> 3 // must be the same byte length as IConstants since this gets replaced with it later
        | IStore _ -> 2
        | IForget _ -> 2
        | IFind _ -> 5
        | IOverwrite _ -> 5
        | ICall _ -> 5
        | ITailCall _ -> 5
        | IOffset _ -> 5
        | IJumpIf _ -> 5
        | IJumpIfNot _ -> 5
        | IOffsetIf _ -> 5
        | IOffsetIfNot _ -> 5
        | IClosure (_, _, closed) -> 8 + 4 * closed.Length
        | IRecursive (_, _, closed) -> 8 + 4 * closed.Length
        | IMutual _ -> 2
        | ICallNative _ -> 5
        | IRequestPermission _ -> 5
        | IHasPermission _ -> 5
        | IJumpPermission _ -> 9
        | IOffsetPermission _ -> 9
        | IHandle _ -> 9
        | IEscape _ -> 6
        | IInject _ -> 5
        | IEject _ -> 5
        | IConstruct _ -> 6
        | IIsStruct _ -> 5
        | IJumpStruct _ -> 9
        | IOffsetStruct _ -> 9
        | IRecordExtend _ -> 5
        | IRecordSelect _ -> 5
        | IVariant _ -> 5
        | IIsCase _ -> 5
        | IJumpCase _ -> 9
        | IOffsetCase _ -> 9

        | II8 _ -> 2
        | IU8 _ -> 2
        | II16 _ -> 3
        | IU16 _ -> 3
        | II32 _ -> 5
        | IU32 _ -> 5
        | IINative _ -> sizeof<nativeint> + 1
        | IUNative _ -> sizeof<unativeint> + 1
        | II64 _ -> 9
        | IU64 _ -> 9
        | ISingle _ -> 5
        | IDouble _ -> 9
        | IRune _ -> 5

        | _ -> 1

    let codeByteLength = List.sumBy instructionByteLength

    let blockInstructions block =
        match block with
        | BUnlabeled ls -> ls
        | BLabeled (_, ls) -> ls

    let blockLength block = List.length (blockInstructions block)

    let blockByteLength block = List.sumBy instructionByteLength (blockInstructions block)

    let delabelBytes blocks =
        let lengths = List.map blockByteLength blocks
        let (startIndices, endInd) = List.mapFold (fun indAcc len -> indAcc, indAcc + len) 0 lengths
        let labelPointers =
            List.fold2
                (fun ptrs block ind ->
                    match block with
                    | BLabeled (label, _) -> Map.add label ind ptrs
                    | _ -> ptrs)
                Map.empty blocks startIndices
        { Labels = labelPointers;
          Instructions = List.map blockInstructions blocks |> List.concat }