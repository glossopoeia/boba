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
        FunLitId: ref<int>;
        OpId: ref<int>;
        RetId: ref<int>;
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
            
            let retId = !program.RetId
            let retName = "funLit" + retId.ToString()
            program.RetId := retId + 1
            let cf = closureFrame env (exprFree r)
            let argEntries = [for p in List.rev ps do { Name = p; Kind = EnvValue }]
            let closedEntries = List.map (fun (_, _, e) -> e) cf |> List.append argEntries
            let closedFinds = List.map (fun (f, i, _) -> (f, i)) cf
            let (retg, retb) = genExpr program (closedEntries :: env) r
            let retBlk = BLabeled (retName, retg)
            let retInstr = IClosure (Label retName, closedFinds)

            ([], [])
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
            let funId = !program.FunLitId
            let funName = "funLit" + funId.ToString()
            program.FunLitId := funId + 1
            let cf = closureFrame env (exprFree b)
            let closedEntries = List.map (fun (_, _, e) -> e) cf
            let closedFinds = List.map (fun (f, i, _) -> (f, i)) cf
            let (flg, flb) = genExpr program (closedEntries :: env) b
            ([IClosure (Label funName, closedFinds)], BLabeled (funName, flg) :: flb)
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
    and genRetBlock program env expr =
        let retId = program.RetId
        let retName = "ret" + (!retId).ToString()
        let b = genBlock program env retName expr
        program.RetId := !retId + 1
        (retName, b)
    and genBlock program env blockName expr =
        let ff = freeFrame expr
        let (blockExpr, subBlocks) = genExpr program ff expr
        BLabeled (blockName, blockExpr) :: subBlocks

    let genMain program =
        genBlock program [] "main" program.Main

    let genProgram program =
        let mainByteCode = genMain program
        let defsByteCodes = genDefs program.Definitions program.Constructors
        let endByteCode = BLabeled ("end", [INop])
        let entryByteCode = BUnlabeled [ICall (Label "main"); ITailCall (Label "end")]
        List.concat [[entryByteCode]; mainByteCode; defsByteCodes; [endByteCode]]