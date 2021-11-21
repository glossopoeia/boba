namespace Mochi.Core

module Instructions =

    type IntegerSize =
        | I8 | U8
        | I16 | U16
        | I32 | U32
        | I64 | U64
        | ISize | USize

    type FloatSize =
        | Single
        | Double

    type JumpTarget =
        | Label of string
        | Index of int

    type Instruction =
        /// No op, doesn't do anything, moves on to the next instruction
        | INop
        /// Placeholder for breakpoints when debugging.
        | IBreakpoint
        /// Terminate the current fiber.
        | IAbort of reason: int
        /// Given an index into the constant pool, place the value at that index on top of the stack.
        | IConstant of poolIndex: int

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
        | IOverwrite of frame: int * index: int
        /// Pop the top of the frame stack.
        | IForget
        /// Get the value stored in the given frame at the given index and put it on top of the stack.
        | IFind of frame: int * index: int
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
        | IClosure of body: JumpTarget * args: int * closed: List<(int * int)>
        /// Push a recursive closure for the given pointer to a function body, storing references to the values in the frame
        /// stack referenced by the list of values to 'close' over. The reference to the closure itself is stored at index 0
        /// of the closed values list.
        | IRecursive of body: JumpTarget * args: int * closed: List<(int * int)>
        /// Given a list of n closures on top of the stack, make them all mutually recursive with respect to each other by
        /// inserting references to each other into their stored closed values. The layout of references is the same for each
        /// closure environment: closure at the top of the stack becomes item 0 in the closed list, closure one down from the
        /// top becomes item 1 in the closed list, etc.
        | IMutual of count: int

        | IHandle of handleId: int * after: int * args: int * operations: List<string>
        | IInject of handleId: int
        | IEject of handleId: int
        | IComplete
        | IEscape of operation: string
        | ICallContinuation
        | ITailCallContinuation

        | IZap
        | IDup
        | ISwap
        | IShuffle of count: int * indices: List<int>
        
        | IJumpIf of target: JumpTarget
        | IJumpIfNot of target: JumpTarget
        | IJumpStruct of ctorId: int * target: JumpTarget
        | IJumpPermission of permId: int
        
        | IOffsetIf of relative: int
        | IOffsetIfNot of relative: int
        | IOffsetStruct of ctorId: int * relative: int
        | IOffsetPermission of permId: int

        | INewRef
        | IGetRef
        | IPutRef

        | IConstruct of ctorId: int * args: int
        | IDestruct
        | IIsStruct of ctorId: int

        | IEmptyRecord
        | IRecordExtend of string
        | IRecordRestrict of string
        | IRecordSelect of string
        | IRecordUpdate of string

        | IEmptyVariant
        | IVariantLabel of label: int
        | IVariantEmbed of label: int
        | IJumpCase of label: int * target: JumpTarget
        | IOffsetCase of label: int * relative: int

        | IListNil
        | IListCons
        | IListSnoc
        | IListHead
        | IListLast
        | IListTail
        | IListInit
        | IListAppend
        | IListIsEmpty

        | ITrue
        | IFalse
        | IBoolNot
        | IBoolAnd
        | IBoolOr
        | IBoolXor
        | IBoolEq

        | II8 of value: sbyte
        | IU8 of value: byte
        | II16 of value: int16
        | IU16 of value: uint16
        | II32 of value: int32
        | IU32 of value: uint32
        | II64 of value: int64
        | IU64 of value: uint64
        | IISize of value: int
        | IUSize of value: uint
        | ISingle of value: single
        | IDouble of value: double
        
        | IIntAdd of IntegerSize
        | IIntAddOvf of IntegerSize
        | IIntSub of IntegerSize
        | IIntSubOvf of IntegerSize
        | IIntMul of IntegerSize
        | IIntMulOvf of IntegerSize
        | IIntDivRemT of IntegerSize
        | IIntDivRemF of IntegerSize
        | IIntDivRemE of IntegerSize
        | IIntOr of IntegerSize
        | IIntAnd of IntegerSize
        | IIntXor of IntegerSize
        | IIntComplement of IntegerSize
        | IIntShiftLeft of IntegerSize
        | IIntArithShiftRight of IntegerSize
        | IIntLogicShiftRight of IntegerSize
        | IIntEqual of IntegerSize
        | IIntLessThan of IntegerSize
        | IIntGreaterThan of IntegerSize
        | IIntSign of IntegerSize

        | IFloatAdd of FloatSize
        | IFloatSub of FloatSize
        | IFloatMul of FloatSize
        | IFloatDiv of FloatSize
        | IFloatEqual of FloatSize
        | IFloatLessThan of FloatSize
        | IFloatGreaterThan of FloatSize
        | IFloatSign of FloatSize

    type Block =
        | BUnlabeled of List<Instruction>
        | BLabeled of string * List<Instruction> 

    let blockInstructions block =
        match block with
        | BUnlabeled ls -> ls
        | BLabeled (_, ls) -> ls

    let blockLength block = List.length (blockInstructions block)
