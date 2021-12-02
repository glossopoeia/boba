namespace Boba.Compiler

module MochiGen =

    open System
    open Boba.Compiler.CoreGen
    open Boba.Core.Common
    open Boba.Core.Syntax
    open Mochi.Core.Instructions
    open Mochi.Core

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
    
    let genFloat size digits =
        match size with
        | Boba.Core.Types.Single -> ISingle (System.Single.Parse digits)
        | Boba.Core.Types.Double -> IDouble (System.Double.Parse digits)
    
    let genBoolIntConv isize =
        let sizeSuffix = isize.ToString().ToLower()
        Map.empty
        |> Map.add ("conv-bool-" + sizeSuffix) [IConvBoolInt isize]
        |> Map.add ("conv-" + sizeSuffix + "-bool") [IConvIntBool isize]

    let genBoolFloatConv fsize =
        let sizeSuffix = fsize.ToString().ToLower()
        Map.empty
        |> Map.add ("conv-bool-" + sizeSuffix) [IConvBoolFloat fsize]
        |> Map.add ("conv-" + sizeSuffix + "-bool") [IConvFloatBool fsize]
    
    let genIntIntConv isize1 isize2 =
        let sizeSuffix1 = isize1.ToString().ToLower()
        let sizeSuffix2 = isize2.ToString().ToLower()
        Map.empty
        |> Map.add ("conv-" + sizeSuffix1 + "-" + sizeSuffix2) [IConvIntInt (isize1, isize2)]
        |> Map.add ("conv-" + sizeSuffix2 + "-" + sizeSuffix1) [IConvIntInt (isize2, isize1)]
    
    let genIntFloatConv isize fsize =
        let sizeSuffix1 = isize.ToString().ToLower()
        let sizeSuffix2 = fsize.ToString().ToLower()
        Map.empty
        |> Map.add ("conv-" + sizeSuffix1 + "-" + sizeSuffix2) [IConvIntFloat (isize, fsize)]
        |> Map.add ("conv-" + sizeSuffix2 + "-" + sizeSuffix1) [IConvFloatInt (fsize, isize)]

    let genIntConv isize =
        genIntIntConv isize I8
        |> mapUnion fst (genIntIntConv isize U8)
        |> mapUnion fst (genIntIntConv isize I16)
        |> mapUnion fst (genIntIntConv isize U16)
        |> mapUnion fst (genIntIntConv isize I32)
        |> mapUnion fst (genIntIntConv isize U32)
        |> mapUnion fst (genIntIntConv isize I64)
        |> mapUnion fst (genIntIntConv isize U64)
        |> mapUnion fst (genIntFloatConv isize Single)
        |> mapUnion fst (genIntFloatConv isize Double)
    
    let genFloatFloatConv fsize1 fsize2 =
        let sizeSuffix1 = fsize1.ToString().ToLower()
        let sizeSuffix2 = fsize2.ToString().ToLower()
        Map.empty
        |> Map.add ("conv-" + sizeSuffix1 + "-" + sizeSuffix2) [IConvFloatFloat (fsize1, fsize2)]
        |> Map.add ("conv-" + sizeSuffix2 + "-" + sizeSuffix2) [IConvFloatFloat (fsize2, fsize1)]

    let genIntPrimVar isize =
        let sizeSuffix = isize.ToString().ToLower()
        Map.empty
        |> Map.add ("neg-" + sizeSuffix) [IIntNeg isize]
        |> Map.add ("inc-" + sizeSuffix) [IIntInc isize]
        |> Map.add ("dec-" + sizeSuffix) [IIntDec isize]
        |> Map.add ("add-" + sizeSuffix) [IIntAdd isize]
        |> Map.add ("addovf-" + sizeSuffix) [IIntAddOvf isize]
        |> Map.add ("sub-" + sizeSuffix) [IIntSub isize]
        |> Map.add ("subovf-" + sizeSuffix) [IIntSubOvf isize]
        |> Map.add ("mul-" + sizeSuffix) [IIntMul isize]
        |> Map.add ("mulovf-" + sizeSuffix) [IIntMulOvf isize]
        |> Map.add ("divremt-" + sizeSuffix) [IIntDivRemT isize]
        |> Map.add ("divremf-" + sizeSuffix) [IIntDivRemF isize]
        |> Map.add ("divreme-" + sizeSuffix) [IIntDivRemE isize]
        |> Map.add ("or-" + sizeSuffix) [IIntOr isize]
        |> Map.add ("and-" + sizeSuffix) [IIntAnd isize]
        |> Map.add ("xor-" + sizeSuffix) [IIntXor isize]
        |> Map.add ("compl-" + sizeSuffix) [IIntComplement isize]
        |> Map.add ("shl-" + sizeSuffix) [IIntShiftLeft isize]
        |> Map.add ("ashr-" + sizeSuffix) [IIntArithShiftRight isize]
        |> Map.add ("lshr-" + sizeSuffix) [IIntLogicShiftRight isize]
        |> Map.add ("eq-" + sizeSuffix) [IIntEqual isize]
        |> Map.add ("lt-" + sizeSuffix) [IIntLessThan isize]
        |> Map.add ("gt-" + sizeSuffix) [IIntGreaterThan isize]
        |> Map.add ("sign-" + sizeSuffix) [IIntSign isize]

    let genFloatPrimvar fsize =
        let sizeSuffix = fsize.ToString().ToLower()
        Map.empty
        |> Map.add ("neg- " + sizeSuffix) [IFloatNeg fsize]
        |> Map.add ("add- " + sizeSuffix) [IFloatAdd fsize]
        |> Map.add ("sub- " + sizeSuffix) [IFloatSub fsize]
        |> Map.add ("mul- " + sizeSuffix) [IFloatMul fsize]
        |> Map.add ("div- " + sizeSuffix) [IFloatDiv fsize]
        |> Map.add ("eq- " + sizeSuffix) [IFloatEqual fsize]
        |> Map.add ("less- " + sizeSuffix) [IFloatLess fsize]
        |> Map.add ("greater- " + sizeSuffix) [IFloatGreater fsize]
        |> Map.add ("sign- " + sizeSuffix) [IFloatSign fsize]

    let convPrimMap =
        genBoolIntConv I8
        |> mapUnion fst (genBoolIntConv U8)
        |> mapUnion fst (genBoolIntConv I16)
        |> mapUnion fst (genBoolIntConv U16)
        |> mapUnion fst (genBoolIntConv I32)
        |> mapUnion fst (genBoolIntConv U32)
        |> mapUnion fst (genBoolIntConv I64)
        |> mapUnion fst (genBoolIntConv U64)
        |> mapUnion fst (genBoolFloatConv Single)
        |> mapUnion fst (genBoolFloatConv Double)
        |> mapUnion fst (genIntConv I8)
        |> mapUnion fst (genIntConv U8)
        |> mapUnion fst (genIntConv I16)
        |> mapUnion fst (genIntConv U16)
        |> mapUnion fst (genIntConv I32)
        |> mapUnion fst (genIntConv U32)
        |> mapUnion fst (genIntConv I64)
        |> mapUnion fst (genIntConv U64)
        |> mapUnion fst (genFloatFloatConv Single Double)

    let intPrimMap =
        genIntPrimVar I8
        |> mapUnion fst (genIntPrimVar U8)
        |> mapUnion fst (genIntPrimVar I16)
        |> mapUnion fst (genIntPrimVar U16)
        |> mapUnion fst (genIntPrimVar I32)
        |> mapUnion fst (genIntPrimVar U32)
        |> mapUnion fst (genIntPrimVar I64)
        |> mapUnion fst (genIntPrimVar U64)
        |> mapUnion fst (genIntPrimVar ISize)
        |> mapUnion fst (genIntPrimVar USize)

    let floatPrimMap =
        genFloatPrimvar Single |> mapUnion fst (genFloatPrimvar Double)

    let genPrimVar prim =
        match prim with
        | "dup" -> [IDup]
        | "swap" -> [ISwap]
        | "zap" -> [IZap]

        | "new-ref" -> [INewRef]
        | "get-ref" -> [IGetRef]
        | "put-ref" -> [IPutRef]

        | "nil-record" -> [IEmptyRecord]

        | "bool-true" -> [ITrue]
        | "bool-false" -> [IFalse]
        | "and-bool" -> [IBoolAnd]
        | "or-bool" -> [IBoolOr]
        | "not-bool" -> [IBoolNot]
        | "xor-bool" -> [IBoolXor]
        | "eq-bool" -> [IBoolEq]

        | "nil-list" -> [IListNil]
        | "cons-list" -> [IListCons]
        | "head-list" -> [IListHead]
        | "tail-list" -> [IListTail]
        | "append-list" -> [IListAppend]

        | "string-concat" -> [IStringConcat]
        | "print" -> [IPrint]

        | _ ->
            if Map.containsKey prim convPrimMap
            then convPrimMap.[prim]
            elif Map.containsKey prim intPrimMap
            then intPrimMap.[prim]
            elif Map.containsKey prim floatPrimMap
            then floatPrimMap.[prim]
            else failwith $"Primitive '{prim}' not yet implemented."

    let gfst (f, _, _) = f
    let gsnd (_, s, _) = s
    let gthd (_, _, t) = t

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
            (List.concat [[IOffset (codeByteLength bg)]; bg; cg; [IOffsetIf -(codeByteLength bg)]], List.append cb bb, List.append cc bc)
        | WLetRecs (rs, b) ->
            let recNames = List.map fst rs
            let frame = List.map (fun v -> { Name = v; Kind = EnvClosure }) recNames
            let (bg, bb, bc) = genExpr program (frame :: env) b

            let recGen = [for r in List.rev rs ->
                          let recFree = Set.difference (exprFree (snd r)) (Set.ofList recNames)
                          genClosure program env (fst r) frame recFree 0 (snd r)]

            let recG = List.collect gfst recGen
            let recBs = List.collect gsnd recGen
            let recCs = List.collect gthd recGen
            (List.concat [recG; [IMutual recNames.Length; IStore recNames.Length]; bg; [IForget]], List.append bb recBs, List.append bc recCs)
        | WVars (vs, e) ->
            let frame = List.map (fun v -> { Name = v; Kind = EnvValue }) vs
            let (eg, eb, ec) = genExpr program (frame :: env) e
            (List.concat [[IStore (List.length vs)]; eg; [IForget]], eb, ec)

        | WExtension n -> ([IRecordExtend n], [], [])
        | WRestriction n -> ([IRecordRestrict n], [], [])
        | WSelect n -> ([IRecordSelect n], [], [])

        | WFunctionLiteral b ->
            genClosure program env "funLit" [] (exprFree b) 0 b
        | WInteger (i, s) -> ([genInteger s i], [], [])
        | WString s -> ([IStringPlaceholder s], [], [IStringPlaceholder s])
        | WCallVar n ->
            if envContains env n
            then
                let (frame, ind, entry) = envGet env n
                match entry.Kind with
                | EnvContinuation -> ([IFind (frame, ind); ICallContinuation], [], [])
                | EnvClosure -> ([IFind (frame, ind); ICallClosure], [], [])
                | EnvValue -> failwith $"Bad callvar kind {n}"
            else ([ICall (Label n)], [], [])
        | WValueVar n ->
            let (frame, ind, entry) = envGet env n
            match entry.Kind with
            | EnvValue -> ([IFind (frame, ind)], [], [])
            | _ -> failwith $"Bad valvar kind {n}"
        | WOperatorVar n ->
            if Map.containsKey n program.Handlers
            then
                let hdlr = program.Handlers.Item n
                ([IEscape (hdlr.HandleId, hdlr.HandlerIndex)], [], [])
            else failwith ("Could not find handler: " + n + ", does it have an effect set declared?")
        | WConstructorVar n ->
            let ctor = program.Constructors.[n]
            ([IConstruct (ctor.Id, ctor.Args)], [], [])
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
    and genCallable program env expr =
        let (eg, eb, ec) = genExpr program env expr
        (List.append eg [IReturn], eb, ec)
    and genClosure program env prefix callAppend free args expr =
        let blkId = program.BlockId.Value
        let name = prefix + blkId.ToString()
        program.BlockId.Value <- blkId + 1
        let cf = closureFrame env free
        let closedEntries = List.map (fun (_, _, e) -> e) cf |> List.append callAppend
        let closedFinds = List.map (fun (f, i, _) -> (f, i)) cf
        let (blkGen, blkSub, blkConst) = genCallable program (closedEntries :: env) expr
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
        let (blockExpr, subBlocks, consts) = genCallable program [] expr
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

        let endByteCode = BLabeled ("end", [IAbort 0])
        let entryByteCode = BUnlabeled [ICall (Label "main"); ITailCall (Label "end")]
        List.concat [[entryByteCode]; mainStripped; defsStripped; [endByteCode]], consts