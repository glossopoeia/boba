namespace Boba.Compiler

module MochiGen =

    open System
    open Boba.Compiler.CoreGen
    open Boba.Compiler.Primitives
    open Boba.Core.Common
    open Boba.Core.Syntax
    open Mochi.Core.Instructions

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
    type Env = List<EnvEntry>

    let envContains (env : Env) name = List.exists (fun e -> e.Name = name) env

    let envGet (env : Env) name =
        try
            let (Some entryIndex) = List.tryFindIndex (fun e -> e.Name = name) env
            (entryIndex, env.[entryIndex])
        with
            ex ->
                failwith $"Could not find name '{name}' when compiling"

    let closureFrame env free =
        [for v in free do
         let (entryIndex, entry) = envGet env v
         (entryIndex, { Name = v; Kind = entry.Kind })]

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
    
    let genFloat size digits =
        match size with
        | Boba.Core.Types.Single -> ISingle (System.Single.Parse digits)
        | Boba.Core.Types.Double -> IDouble (System.Double.Parse digits)
    
    let gfst (f, _, _) = f
    let gsnd (_, s, _) = s
    let gthd (_, _, t) = t

    /// Returns a tuple containing:
    /// 1. The list of instructions generated for the word
    /// 2. Any sub-blocks generated during instruction generation
    /// 3. A list of constants generated for the word
    let rec genWord program env word =
        match word with
        | WDo -> ([ICallClosure], [], [])
        | WHandle (ps, h, hs, r) ->
            let (hg, hb, hc) = genExpr program env h
            let handleBody = List.append hg [IComplete]
            
            let hndlThread = [for p in List.rev ps -> { Name = p; Kind = EnvValue }]
            let retFree = Set.difference (exprFree r) (Set.ofList ps)
            let (retG, retBs, retCs) = genClosure program env "ret" hndlThread retFree 0 r

            let genOps =
                [for handler in List.rev hs ->
                 let hdlrArgs = [for p in List.rev handler.Params do { Name = p; Kind = EnvValue }]
                 let hdlrApp = { Name = "resume"; Kind = EnvContinuation } :: (List.append hdlrArgs hndlThread)
                 let hdlrClosed = Set.add "resume" (Set.union (Set.ofList handler.Params) (Set.ofList ps))
                 let hdlrFree = Set.difference (exprFree handler.Body) hdlrClosed
                 genClosure program env handler.Name hdlrApp hdlrFree handler.Params.Length handler.Body]

            let opsG = List.collect gfst genOps
            let opsBs = List.collect gsnd genOps
            let opsCs = List.collect gthd genOps

            // the commented-out offset below only works for the simulator
            //let afterOffset = handleBody.Length + 1
            let afterOffset = codeByteLength handleBody
            let hdlrMeta = program.Handlers.Item hs.Head.Name
            let handle = IHandle (hdlrMeta.HandleId, afterOffset, ps.Length, hs.Length)

            (List.concat [retG; opsG; [handle]; handleBody], List.concat [hb; retBs; opsBs], List.concat [hc; retCs; opsCs])
        | WInject (effs, e) ->
            let hdlrIds = List.map (fun eff -> program.Effects.Item eff) effs
            let (eg, eb, ec) = genExpr program env e
            let injInstrs = List.map IInject hdlrIds
            let ejInstrs = List.map IEject hdlrIds
            (List.concat [injInstrs; eg; ejInstrs;], eb, ec)
        | WIf (b, []) ->
            let (bg, bb, bc) = genExpr program env b
            (List.concat [[IOffsetIfNot (codeByteLength bg)]; bg], bb, bc)
        | WIf (tc, ec) ->
            let (tcg, tcb, tcc) = genExpr program env tc
            let (ecg, ecb, ecc) = genExpr program env ec
            // plus 5 to handle the else offset after the branch on true
            let skipThen = [IOffset (codeByteLength tcg)]
            (List.concat [[IOffsetIf (codeByteLength ecg + codeByteLength skipThen)]; ecg; skipThen; tcg], List.append tcb ecb, List.append tcc ecc)
        | WWhile (c, b) ->
            let (cg, cb, cc) = genExpr program env c
            let (bg, bb, bc) = genExpr program env b
            // + 5 hardcoded here because IOffsetIf will have already been read during runtime
            // it's basically 5 = codeByteLength IOffsetIf, but would need to be self referential
            // without hardcoding
            let repeat = [IOffsetIf -(codeByteLength bg + codeByteLength cg + 5)]
            (List.concat [[IOffset (codeByteLength bg)]; bg; cg; repeat], List.append cb bb, List.append cc bc)
        | WLetRecs (rs, b) ->
            let recNames = List.map fst rs
            let frame = List.map (fun v -> { Name = v; Kind = EnvClosure }) recNames
            let newEnv = List.foldBack (fun v e -> { Name = v; Kind = EnvClosure } :: e) recNames env
            let (bg, bb, bc) = genExpr program newEnv b

            let recGen = [for r in List.rev rs ->
                          let recFree = Set.difference (exprFree (snd r)) (Set.ofList recNames)
                          genClosure program env (fst r) frame recFree 0 (snd r)]

            let recG = List.collect gfst recGen
            let recBs = List.collect gsnd recGen
            let recCs = List.collect gthd recGen
            (List.concat [recG; [IMutual recNames.Length; IStore recNames.Length]; bg; [IForget recNames.Length]], List.append bb recBs, List.append bc recCs)
        | WVars ([], e) -> genExpr program env e
        | WVars (vs, e) ->
            let newEnv = List.foldBack (fun v e -> { Name = v; Kind = EnvValue } :: e) vs env
            let (eg, eb, ec) = genExpr program newEnv e
            (List.concat [[IStore (List.length vs)]; eg; [IForget (List.length vs)]], eb, ec)

        // TODO: GetHashCode is the wrong thing to use here! Need to convert labels to integers
        // in a separate pass and then translate them here from a mapping in the environment.
        | WEmptyRecord -> ([IEmptyRecord], [], [])
        | WExtension n -> ([IRecordExtend (n.GetHashCode())], [], [])
        | WSelect n -> ([IRecordSelect (n.GetHashCode())], [], [])

        // TODO: GetHashCode is the wrong thing to use here! Need to convert labels to integers
        // in a separate pass and then translate them here from a mapping in the environment.
        | WVariantLiteral n -> ([IVariant (n.GetHashCode())], [], [])
        | WCase (n, t, e) ->
            let (tcg, tcb, tcc) = genExpr program env t
            let (ecg, ecb, ecc) = genExpr program env e
            let skipThen = [IOffset (codeByteLength tcg)]
            let header = [IOffsetCase (n.GetHashCode(), codeByteLength ecg + codeByteLength skipThen)]
            (List.concat [header; ecg; skipThen; tcg], List.append tcb ecb, List.append tcc ecc)

        | WFunctionLiteral b ->
            genClosure program env "funLit" [] (exprFree b) 0 b
        | WInteger (i, s) -> ([genInteger s i], [], [])
        | WDecimal (i, s) -> ([genFloat s i], [], [])
        | WString s -> ([IStringPlaceholder s], [], [IStringPlaceholder s])
        | WCallVar n ->
            if envContains env n
            then
                let (ind, entry) = envGet env n
                match entry.Kind with
                | EnvContinuation -> ([IFind (ind); ICallContinuation], [], [])
                | EnvClosure -> ([IFind (ind); ICallClosure], [], [])
                | EnvValue -> failwith $"Bad callvar kind {n}"
            else ([ICall (Label n)], [], [])
        | WValueVar n ->
            let (ind, entry) = envGet env n
            match entry.Kind with
            | EnvValue ->
                ([IFind (ind)], [], [])
            | _ -> failwith $"Bad valvar kind {n} : {entry.Kind}"
        | WOperatorVar n ->
            if Map.containsKey n program.Handlers
            then
                let hdlr = program.Handlers.Item n
                ([IEscape (hdlr.HandleId, hdlr.HandlerIndex)], [], [])
            else failwith ("Could not find handler: " + n + ", does it have an effect set declared?")
        | WConstructorVar n ->
            try
                let ctor = program.Constructors.[n]
                ([IConstruct (ctor.Id, ctor.Args)], [], [])
            with
                | :? System.Collections.Generic.KeyNotFoundException ->
                    Map.iter (fun k v -> printfn $"{k} -> {v}") program.Constructors
                    failwith $"Could not find constructor entry with name '{n}'"
        | WDestruct ->
            ([IDestruct], [], [])
        | WTestConstructorVar n ->
            let ctor = program.Constructors.[n]
            ([IIsStruct ctor.Id], [], [])
        | WPrimVar name -> (genPrimVar name, [], [])
    and genExpr program env expr =
        let res = List.map (genWord program env) expr
        let wordGen = List.map gfst res
        let blockGen = List.map gsnd res
        let constGen = List.map gthd res
        (List.concat wordGen, List.concat blockGen, List.concat constGen)
    and genTailCall hasResume instrs =
        let forgetResume = if hasResume then [IForget 1] else []
        if List.isEmpty instrs
        then (instrs, false)
        else
            let front = List.take (instrs.Length - 1) instrs
            let last = List.last instrs
            match last with
            | ICall n -> append3 front forgetResume [ITailCall n], true
            | ICallClosure -> append3 front forgetResume [ITailCallClosure], true
            | ICallContinuation -> append3 front forgetResume [ITailCallContinuation], true
            | ITailCall n -> append3 front forgetResume [last], true
            | ITailCallClosure -> append3 front forgetResume [last], true
            | ITailCallContinuation -> append3 front forgetResume [last], true
            | _ -> append3 front forgetResume [last], false
    and genCallable program env hasResume expr =
        let (eg, eb, ec) = genExpr program env expr
        let (maybeTailCallE, isTailCall) = genTailCall hasResume eg
        if isTailCall
        then (maybeTailCallE, eb, ec)
        else (List.append maybeTailCallE [IReturn], eb, ec)
    and genClosure program env prefix callAppend free args expr =
        let blkId = program.BlockId.Value
        let name = prefix + blkId.ToString()
        program.BlockId.Value <- blkId + 1
        let cf = closureFrame env free
        let hasResume = List.exists (fun ent -> ent.Name = "resume") callAppend
        let closedEntries = List.map (fun (_, e) -> e) cf |> List.append callAppend
        let closedFinds = List.map (fun (i, _) -> i) cf
        let (blkGen, blkSub, blkConst) = genCallable program (List.append closedEntries env) hasResume expr
        ([IClosure ((Label name), args, closedFinds)], BLabeled (name, blkGen) :: blkSub, blkConst)

    let rec replacePlaceholder consts instr =
        match instr with
        | IStringPlaceholder _ ->
            IConstant ((uint16)(List.findIndex ((=) instr) consts))
        | _ -> instr

    let stripConstants consts blk =
        match blk with
        | BLabeled (l, gen) -> BLabeled (l, gen |> List.map (replacePlaceholder consts))
        | BUnlabeled gen -> BUnlabeled (gen |> List.map (replacePlaceholder consts))
    
    let genBlock program blockName expr =
        let (blockExpr, subBlocks, consts) = genCallable program [] false expr
        BLabeled (blockName, blockExpr) :: subBlocks, consts

    let genMain program =
        genBlock program "main" program.Main

    let genProgram program =
        let mainAndConsts = genMain program
        let defsAndConsts =
            Map.toList program.Definitions
            |> List.map (uncurry (genBlock program))

        let mainByteCode = fst mainAndConsts
        let defsByteCodes = List.collect fst defsAndConsts

        let mainConsts = snd mainAndConsts
        let defsConsts = List.collect snd defsAndConsts
        let consts = List.append mainConsts defsConsts |> List.distinct

        let mainStripped = List.map (stripConstants consts) mainByteCode 
        let defsStripped = List.map (stripConstants consts) defsByteCodes 

        let endByteCode = BLabeled ("end", [IAbort])
        let entryByteCode = BUnlabeled [ICall (Label "main"); ITailCall (Label "end")]
        List.concat [[entryByteCode]; mainStripped; defsStripped; [endByteCode]], consts