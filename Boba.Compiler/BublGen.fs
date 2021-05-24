namespace Boba.Compiler

module BublGen =

    open System
    open Boba.Core.Syntax
    open Bubl.Core.Instructions

    type Constructor = {
        Id: int;
        Args: int
    }

    type TopLevelProg = {
        Main: Expression;
        Definitions: Map<string, Expression>;
        Constructors: Map<string, Constructor>;
    }

    let assocIndexOf key elems =
        List.tryFindIndex (fun (k, _) -> k = key) elems

    let rec envGet env name =
        List.tryFindIndex (fun f -> Option.isSome (assocIndexOf name f)) env
        |> Option.bind (fun frame ->
            assocIndexOf name env.[frame]
            |> Option.map (fun ind -> (frame, ind)))

    let genInteger size digits =
        match size with
        | Boba.Core.Types.I8 -> II8 (SByte.Parse digits)
        | Boba.Core.Types.U8 -> IU8 (Byte.Parse digits)
        | Boba.Core.Types.I16 -> II16 (Int16.Parse digits)
        | Boba.Core.Types.U16 -> IU16 (UInt16.Parse digits)
        | Boba.Core.Types.I32 -> II32 (Int32.Parse digits)
        | Boba.Core.Types.U32 -> IU32 (UInt32.Parse digits)
        | Boba.Core.Types.I64 -> II64 (Int64.Parse digits)
        | Boba.Core.Types.U64 -> IU64 (UInt64.Parse digits)
        | Boba.Core.Types.ISize -> IISize (int digits)
        | Boba.Core.Types.USize -> IUSize (uint digits)

    let rec genWord program env word =
        match word with
        | WHandle (ps, h, hs, r) ->
            let hg = genExpr program env h
        | WIfStruct (ctorName, tc, ec) ->
            let ctor = program.Constructors.[ctorName]
            let tcg = genExpr program env tc
            let ecg = genExpr program env ec
            List.concat [[IOffsetStruct (ctor.Id, List.length ecg)]; ecg; IDestruct :: tcg]
        | WIf (tc, ec) ->
            let tcg = genExpr program env tc
            let ecg = genExpr program env ec
            List.concat [[IOffsetIf (List.length ecg)]; ecg; tcg]
        | WVars (vs, e) ->
            let frame = List.mapi (fun i v -> (v, i)) (List.rev vs)
            let eg = genExpr program (frame :: env) e
            List.concat [[IStore (List.length vs)]; eg; [IForget]]
        | WDo -> [ICallClosure]
        | WInteger (i, s) -> [genInteger s i]
        | WCallVar n ->
            match envGet env n with
            | Some (frame, ind) ->
                if isContinuation n
                then [IFind (frame, ind); ICallContinuation]
                elif isClosure n
                then [IFind (frame, ind); ICallClosure]
                else failwith $"Bad callvar kind {n}"
            | None -> [ICall (Label n)]
        | WValueVar n ->
            match envGet env n with
            | Some (frame, ind) -> [IFind (frame, ind)]
            | None -> failwith $"Bad valvar kind {n}"
        | WOperatorVar n -> [IOperation n]
        | WConstructorVar n ->
            let ctor = program.Constructors.[n]
            [IConstruct (ctor.Id, ctor.Args)]
        | WTestConstructorVar n ->
            let ctor = program.Constructors.[n]
            [IIsStruct ctor.Id]
    and genExpr program env expr =
        List.concat (List.map (genWord program env) expr)

    let genBlock program blockName expr =
        let ff = freeFrame expr
        BLabeled (blockName, genExpr program ff expr)

    let genMain program =
        genBlock program "main" program.Main

    let genProgram program =
        let mainByteCode = genMain program
        let defsByteCodes = genDefs program.Definitions program.Constructors
        let endByteCode = BLabeled ("end", [INop])
        let entryByteCode = BUnlabeled [ICall (Label "main"); ITailCall (Label "end")]
        List.concat [[mainByteCode]; defsByteCodes; [endByteCode]; [entryByteCode]]