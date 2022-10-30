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
        override this.ToString() =
            match this with
            | EnvValue -> $"*"
            | EnvClosure -> $"->"
            | EnvContinuation -> $"!"

    type EnvEntry =
        {
            Name: string;
            Kind: EnvEntryKind;
            Params: List<string>;
            Outputs: int;
        }
        override this.ToString() =
            $"""{this.Name} : {this.Kind} => {String.concat " " this.Params}"""
    
    let valueEntry n = { Name = n; Kind = EnvValue; Params = []; Outputs = 0 }

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
        [for v in free do envGet env v]

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
        | Boba.Core.Types.INative -> IINative (IntPtr.Parse digits)
        | Boba.Core.Types.UNative -> IUNative (UIntPtr.Parse digits)
    
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
        | WNursery (n, body) ->
            let genBody, genBlk, genCnst = genExpr program (valueEntry n :: env) body
            List.concat [[INewNursery; IStore 1]; genBody; [IFind 0; IWaitNursery; IForget 1]], genBlk, genCnst
        | WCancellable (n, body) ->
            let genBody, genBlk, genCnst = genExpr program (valueEntry n :: env) body
            List.concat [[IPushCancel; IStore 1]; genBody; [IPopContext; IForget 1]], genBlk, genCnst
        | WHandle (ps, h, hs, r) ->
            let hndlThread = [for p in List.rev ps -> valueEntry p]
            let (hg, hb, hc) = genExpr program (List.append hndlThread env) h

            let hdlrEnv = List.append hndlThread env
            
            let retFree = Set.difference (exprFree (snd r)) (Set.ofList (List.append (fst r) ps))
            let retArgs = [for a in List.rev (fst r) -> valueEntry a]
            let ((retG : List<Instruction>), retBs, retCs) = genClosure program env hdlrEnv "ret" retArgs retFree false (snd r)
            
            let handleBody = append3 hg retG [ICallClosure]

            let genOps =
                [for handler in List.rev hs ->
                 let hdlrMeta = program.Handlers.Item handler.Name
                 let hdlrArgs = [for p in List.rev handler.Params do valueEntry p]
                 let hdlrApp = { Name = "resume"; Kind = EnvContinuation; Params = List.rev ps; Outputs = hdlrMeta.Outputs } :: hdlrArgs
                 let hdlrClosed = Set.add "resume" (Set.union (Set.ofList handler.Params) (Set.ofList ps))
                 let hdlrFree = Set.difference (exprFree handler.Body) hdlrClosed
                 genClosure program env hdlrEnv handler.Name hdlrApp hdlrFree true handler.Body]

            let opsG = List.collect gfst genOps
            let opsBs = List.collect gsnd genOps
            let opsCs = List.collect gthd genOps

            let afterOffset = codeByteLength handleBody
            let hdlrMeta = program.Handlers.Item hs.Head.Name
            let handle = IHandle (hdlrMeta.HandleId, afterOffset, ps.Length, hs.Length)

            (List.concat [opsG; [handle]; handleBody; [IRestore]], List.concat [hb; retBs; opsBs], List.concat [hc; retCs; opsCs])
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
        | WHasPermission perm -> [IHasPermission (Label perm)], [], []
        | WRequestPermission perm -> [IRequestPermission (Label perm)], [], []
        | WLetRecs (rs, b) ->
            let recNames = List.map fst rs
            let frame = List.map valueEntry recNames
            let newEnv = List.foldBack (fun v e -> valueEntry v :: e) recNames env
            let (bg, bb, bc) = genExpr program newEnv b

            let recGen = [for r in List.rev rs ->
                          let recFree = Set.difference (exprFree (snd r)) (Set.ofList recNames)
                          genClosure program env env (fst r) frame recFree false (snd r)]

            let recG = List.collect gfst recGen
            let recBs = List.collect gsnd recGen
            let recCs = List.collect gthd recGen
            (List.concat [recG; [IMutual recNames.Length; IStore recNames.Length]; bg; [IForget recNames.Length]], List.append bb recBs, List.append bc recCs)
        | WVars ([], e) -> genExpr program env e
        | WVars (vs, e) ->
            let newEnv = List.foldBack (fun v e -> valueEntry v :: e) vs env
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
            genClosure program env env "funLit" [] (exprFree b) false b
        | WInteger (i, s) -> ([genInteger s i], [], [])
        | WDecimal (i, s) -> ([genFloat s i], [], [])
        | WString s -> ([IStringPlaceholder s], [], [IStringPlaceholder s])
        | WChar c -> [IRune c], [], []
        | WCallVar n ->
            if envContains env n
            then
                let (ind, entry) = envGet env n
                match entry.Kind with
                | EnvContinuation ->
                    printfn $"{n} params: {entry.Params}"
                    printfn $"""{n} env: {String.concat ", " [for e in env -> $"{e}"]}"""
                    let overwrites = [for p in entry.Params -> WOverwriteValueVar p]
                    let genOverwrites, _, _ = [for o in overwrites -> genWord program env o] |> List.unzip3
                    (List.append (List.concat genOverwrites) [IFind (ind); ICallContinuation entry.Outputs], [], [])
                | EnvClosure -> ([IFind (ind); ICallClosure], [], [])
                | EnvValue -> failwith $"Bad callvar kind {n}"
            else ([ICall (Label n)], [], [])
        | WNativeVar n ->
            [ICallNative (Label n)], [], []
        | WValueVar n ->
            let (ind, entry) = envGet env n
            match entry.Kind with
            | EnvValue ->
                ([IFind (ind)], [], [])
            | _ -> failwith $"Bad valvar kind {n} : {entry.Kind}"
        | WOverwriteValueVar n ->
            let (ind, entry) = envGet env n
            match entry.Kind with
            | EnvValue ->
                ([IOverwrite (ind)], [], [])
            | _ -> failwith $"Bad valvar kind {n} : {entry.Kind}"
        | WOperatorVar n ->
            if Map.containsKey n program.Handlers
            then
                let hdlr = program.Handlers.Item n
                ([IEscape (hdlr.HandleId, hdlr.HandlerIndex, hdlr.Inputs)], [], [])
            else failwith ("Could not find handler: " + n + ", does it have an effect set declared?")
        | WConstructorVar n ->
            try
                let ctor = program.Constructors.[n]
                ([IConstruct (ctor.Id, ctor.Args)], [], [])
            with
                | :? System.Collections.Generic.KeyNotFoundException ->
                    failwith $"Could not find constructor entry with name '{n}'"
        | WDestruct ->
            ([IDestruct], [], [])
        | WTestConstructorVar n ->
            let ctor = program.Constructors.[n]
            ([IIsStruct ctor.Id], [], [])
    and genExpr program env expr =
        let res = List.map (genWord program env) expr
        let wordGen = List.map gfst res
        let blockGen = List.map gsnd res
        let constGen = List.map gthd res
        (List.concat wordGen, List.concat blockGen, List.concat constGen)
    and genFunction forgetCount instrs =
        let forget = if forgetCount > 0 then [IForget forgetCount] else []
        if List.isEmpty instrs
        then [IReturn]
        else
            let front = List.take (instrs.Length - 1) instrs
            let last = List.last instrs
            match last with
            | ICall n -> append3 front forget [ITailCall n]
            | ICallClosure -> append3 front forget [ITailCallClosure]
            | ITailCall n -> append3 front forget [last]
            | ITailCallClosure -> append3 front forget [last]
            | _ -> append3 instrs forget [IReturn]
    and genHandler forgetCount instrs =
        let forget = if forgetCount > 0 then [IForget forgetCount] else []
        if List.isEmpty instrs
        then [IRestore]
        else
            let front = List.take (instrs.Length - 1) instrs
            let last = List.last instrs
            match last with
            | ICallContinuation o -> append3 front forget [ITailCallContinuation o]
            | ITailCallContinuation _ -> append3 front forget [last]
            | _ -> append3 instrs forget [IComplete]
    and genCallable program env forgetCount isHdlr expr =
        let (eg, eb, ec) = genExpr program env expr
        let maybeTailCallE = if isHdlr then genHandler forgetCount eg else genFunction forgetCount eg
        maybeTailCallE, eb, ec
    and genClosure program capEnv closEnv prefix callAppend free isHdlr expr =
        let blkId = program.BlockId.Value
        let name = prefix + blkId.ToString()
        program.BlockId.Value <- blkId + 1
        let cf = closureFrame capEnv free
        let closedEntries = List.map (fun (_, e) -> e) cf |> List.append callAppend
        let forgetCount = List.length closedEntries
        let closedFinds = List.map (fun (i, _) -> i) cf |> List.rev
        let (blkGen, blkSub, blkConst) = genCallable program (List.append closedEntries closEnv) forgetCount isHdlr expr
        ([IClosure ((Label name), closedFinds)], BLabeled (name, blkGen) :: blkSub, blkConst)

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
        let (blockExpr, subBlocks, consts) = genCallable program [] 0 false expr
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
        program.Natives, List.concat [[entryByteCode]; mainStripped; defsStripped; [endByteCode]], consts