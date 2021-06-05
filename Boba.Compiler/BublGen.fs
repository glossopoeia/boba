namespace Boba.Compiler

module BublGen =

    open System
    open Boba.Core.Common
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
        BlockId: ref<int>;
    }

    /// It is helpful to distinguish between variables that were bound as values vs as functions, because the
    /// latter have a different semantics for the name appearing in the source code (push and call, vs just push).
    /// Continuations have their own special instructions for being called, which is why it is necessary to distinguish
    /// between closures and continuations.
    type EnvEntryKind =
        | EnvValue
        | EnvClosure
        | EnvContinuation

    type EnvEntry = {
        Name: string;
        Kind: EnvEntryKind;
    }

    /// An environment is a stack of 'call frames', each of which is an ordered list of variables
    /// with some information attached to each variable.
    type Env = List<List<EnvEntry>>

    let envContains (env : Env) name = List.exists (List.exists (fun e -> e.Name = name)) env

    let envGet (env : Env) name =
        let (Some frameIndex) = List.tryFindIndex (List.exists (fun e -> e.Name = name)) env
        let (Some entryIndex) = List.tryFindIndex (fun e -> e.Name = name) env.[frameIndex]
        (frameIndex, entryIndex, env.[frameIndex].[entryIndex])

    let closureFrame env free =
        [for v in free do
         let (frameIndex, entryIndex, entry) = envGet env v
         (frameIndex, entryIndex, { Name = v; Kind = entry.Kind })]

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
        | WDo -> ([ICallClosure], [])
        | WHandle (ps, h, hs, r) ->
            let (hg, hb) = genExpr program env h
            let handleBody = List.append hg [IComplete]
            
            let hndlThread = [for p in List.rev ps -> { Name = p; Kind = EnvValue }]
            let retFree = Set.difference (exprFree r) (Set.ofList ps)
            let (retG, retBs) = genBasicClosure program env "ret" hndlThread retFree r

            let genOps =
                [for handler in hs ->
                 let hdlrArgs = [for p in List.rev handler.Params do { Name = p; Kind = EnvValue }]
                 let hdlrApp = { Name = "resume"; Kind = EnvContinuation } :: (List.append hdlrArgs hndlThread)
                 let hdlrFree = Set.difference (exprFree handler.Body) (Set.union (Set.ofList handler.Params) (Set.ofList ps))
                 genOpClosure program env handler.Name hdlrApp hdlrFree handler.Params.Length handler.Body]

            let opsG = List.map fst genOps |> List.concat
            let opsBs = List.map snd genOps |> List.concat

            let handle = IHandle (handleBody.Length, ps.Length, [for h in hs -> h.Name])

            (List.concat [retG; opsG; [handle]; handleBody], List.concat [hb; retBs; opsBs])
        | WIfStruct (ctorName, tc, ec) ->
            let ctor = program.Constructors.[ctorName]
            let (tcg, tcb) = genExpr program env tc
            let (ecg, ecb) = genExpr program env ec
            (List.concat [[IOffsetStruct (ctor.Id, List.length ecg)]; ecg; IDestruct :: tcg], List.append tcb ecb)
        | WIf (tc, ec) ->
            let (tcg, tcb) = genExpr program env tc
            let (ecg, ecb) = genExpr program env ec
            (List.concat [[IOffsetIf (List.length ecg)]; ecg; tcg], List.append tcb ecb)
        | WVars (vs, e) ->
            let frame = List.map (fun v -> { Name = v; Kind = EnvValue }) (List.rev vs)
            let (eg, eb) = genExpr program (frame :: env) e
            (List.concat [[IStore (List.length vs)]; eg; [IForget]], eb)
        | WFunctionLiteral b ->
            genBasicClosure program env "funLit" [] (exprFree b) b
        | WInteger (i, s) -> ([genInteger s i], [])
        | WCallVar n ->
            if envContains env n
            then
                let (frame, ind, entry) = envGet env n
                match entry.Kind with
                | EnvContinuation -> ([IFind (frame, ind); ICallContinuation], [])
                | EnvClosure -> ([IFind (frame, ind); ICallClosure], [])
                | EnvValue -> failwith $"Bad callvar kind {n}"
            else ([ICall (Label n)], [])
        | WValueVar n ->
            let (frame, ind, entry) = envGet env n
            match entry.Kind with
            | EnvValue -> ([IFind (frame, ind)], [])
            | _ -> failwith $"Bad valvar kind {n}"
        | WOperatorVar n -> ([IOperation n], [])
        | WConstructorVar n ->
            let ctor = program.Constructors.[n]
            ([IConstruct (ctor.Id, ctor.Args)], [])
        | WTestConstructorVar n ->
            let ctor = program.Constructors.[n]
            ([IIsStruct ctor.Id], [])
    and genExpr program env expr =
        let res = List.map (genWord program env) expr
        let wordGen = List.map fst res
        let blockGen = List.map snd res
        (List.concat wordGen, List.concat blockGen)
    and genCallable program env expr =
        let (eg, eb) = genExpr program env expr
        (List.append eg [IReturn], eb)
    and genClosure program env prefix callAppend free ctor expr =
        let blkId = !program.BlockId
        let name = prefix + blkId.ToString()
        program.BlockId := blkId + 1
        let cf = closureFrame env free
        let closedEntries = List.map (fun (_, _, e) -> e) cf |> List.append callAppend
        let closedFinds = List.map (fun (f, i, _) -> (f, i)) cf
        let (blkGen, blkSub) = genCallable program (closedEntries :: env) expr
        ([ctor (Label name) closedFinds], BLabeled (name, blkGen) :: blkSub)
    and genBasicClosure program env prefix callAppend free expr =
        genClosure program env prefix callAppend free (curry IClosure) expr
    and genOpClosure program env prefix callAppend free args expr =
        genClosure program env prefix callAppend free (fun n vs -> IOperationClosure(n, args, vs)) expr
    
    let genBlock program blockName expr =
        let (blockExpr, subBlocks) = genCallable program [] expr
        BLabeled (blockName, blockExpr) :: subBlocks

    let genMain program =
        genBlock program "main" program.Main

    let genProgram program =
        let mainByteCode = genMain program
        let defsByteCodes = Map.toList program.Definitions |> List.map (uncurry (genBlock program)) |> List.concat
        let endByteCode = BLabeled ("end", [INop])
        let entryByteCode = BUnlabeled [ICall (Label "main"); ITailCall (Label "end")]
        List.concat [[entryByteCode]; mainByteCode; defsByteCodes; [endByteCode]]