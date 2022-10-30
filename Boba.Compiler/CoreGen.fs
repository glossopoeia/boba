namespace Boba.Compiler

module CoreGen =

    open System
    open Boba.Core
    open Boba.Core.Common
    open Boba.Core.Fresh
    open Boba.Core.Syntax
    open Boba.Compiler.Condenser
    open Boba.Compiler.Primitives

    type EnvEntry = {
        Callable: bool;
        Native: bool;
        Empty: bool
    }

    type Constructor = {
        Id: int;
        Args: int
    }

    type HandlerMeta = {
        HandleId: int;
        HandlerIndex: int;
        Inputs: int;
        Outputs: int;
    }

    type Native = {
        UnitName: string;
        Imports: List<Syntax.ImportPath>;
        Decls: Map<string, List<Syntax.NativeCodeLine>>
    }

    type TopLevelProg = {
        Main: Expression;
        Definitions: Map<string, Expression>;
        Constructors: Map<string, Constructor>;
        Handlers: Map<string, HandlerMeta>;
        Effects: Map<string, int>;
        Natives: List<Native>;
        BlockId: ref<int>;
    }

    let varEntry = { Callable = false; Native = false; Empty = false }
    let natEntry = { Callable = true; Native = true; Empty = false }

    let rec genCoreWord fresh env word =
        match word with
        | Syntax.EStatementBlock ss -> genCoreStatements fresh env ss
        | Syntax.ENursery (n, ss) ->
            let genSs = genCoreStatements fresh (Map.add n.Name varEntry env) ss
            [WNursery (n.Name, genSs)]
        | Syntax.ECancellable (n, ss) ->
            let genSs = genCoreStatements fresh (Map.add n.Name varEntry env) ss
            [WCancellable (n.Name, genSs)]
        | Syntax.EHandle (rc, ps, h, hs, r) ->
            let hg = genCoreStatements fresh env h
            let pars = List.map (fun (id : Syntax.Name) -> id.Name) ps
            let hEnv = List.fold (fun e n -> Map.add n varEntry e) env pars
            let hgs = List.map (genHandler fresh hEnv) hs
            let rEnv = List.fold (fun e n -> Map.add n varEntry e) hEnv (List.ofSeq (Syntax.namesToStrings (fst r)))
            let rg = genCoreExpr fresh rEnv (snd r)
            [WHandle (pars, hg, hgs, (List.map Syntax.nameToString (fst r), rg))]
        | Syntax.EInject (ns, ss) ->
            let effs = List.map (fun (id : Syntax.Identifier) -> id.Name.Name) ns
            let inj = genCoreStatements fresh env ss
            [WInject (effs, inj)]
        | Syntax.EMatch (cs, o) ->
            let genO = genCoreExpr fresh env o
            if cs.Length = 1
            then genSingleMatch fresh env cs.[0] genO
            else genHandlePatternMatches fresh env cs genO
        | Syntax.EIf (c, t, e) ->
            let cg = genCoreExpr fresh env c
            let tg = genCoreStatements fresh env t
            let eg = genCoreStatements fresh env e
            List.append cg [WIf (tg, eg)]
        | Syntax.EWhile (c, b) ->
            let cg = genCoreExpr fresh env c
            let bg = genCoreStatements fresh env b
            [WWhile (cg, bg)]
        | Syntax.EForEffect (assign, body) ->
            genCoreForEffect fresh env assign body
        | Syntax.EForComprehension (res, assign, body) ->
            let resVars = [for r in res -> (fresh.Fresh "$mapRes", r)]
            genCoreForComp fresh env resVars resVars assign body
        | Syntax.EForFold (accs, assign, body) ->
            genCoreForFold fresh env accs (List.rev [for a in accs -> a.Name.Name]) assign body
        | Syntax.EWithPermission (perms, withSs, elseSs) ->
            let withGen = genCoreStatements fresh env withSs
            let elseGen = genCoreStatements fresh env elseSs
            let checkPerm = List.fold (fun e (p: Syntax.Name) -> List.append e [WRequestPermission p.Name; primAndBool]) [primTrueBool] perms
            List.append checkPerm [WIf (withGen, elseGen)]
        | Syntax.EIfPermission (perms, withSs, elseSs) ->
            let withGen = genCoreStatements fresh env withSs
            let elseGen = genCoreStatements fresh env elseSs
            let checkPerm = List.fold (fun e (p: Syntax.Name) -> List.append e [WHasPermission p.Name; primAndBool]) [primTrueBool] perms
            List.append checkPerm [WIf (withGen, elseGen)]
        | Syntax.EForgetPermission _ -> raise (new NotImplementedException("CoreGen - EForgetPermission"))

        | Syntax.EFunctionLiteral e -> [WFunctionLiteral (genCoreExpr fresh env e)]
        | Syntax.ETupleLiteral [] -> [primNilTuple]
        // TODO: tuple literals with a splat expression may need some adjustment here, to support
        // splatting in the main expression if we want
        | Syntax.ETupleLiteral exp -> genCoreExpr fresh env exp
        | Syntax.EListLiteral [] -> [primNilList]
        | Syntax.EListLiteral exp -> genCoreExpr fresh env exp

        | Syntax.ERecordLiteral [] -> [WEmptyRecord]
        | Syntax.ERecordLiteral exp -> genCoreExpr fresh env exp
        | Syntax.EExtension n -> [WExtension n.Name]
        | Syntax.ESelect (true, n) -> [WSelect n.Name]
        | Syntax.ESelect (false, n) -> [primDup; WSelect n.Name]

        | Syntax.EVariantLiteral (n, exp) -> List.append (genCoreExpr fresh env exp) [WVariantLiteral n.Name]
        | Syntax.ECase ([], _) -> failwith "Improper case statement encountered during core code generation."
        | Syntax.ECase ([c], o) -> [WCase (c.Tag.Name, genCoreExpr fresh env c.Body, genCoreExpr fresh env o)]
        | Syntax.ECase (c :: cs, o) -> [WCase (c.Tag.Name, genCoreExpr fresh env c.Body, genCoreWord fresh env (Syntax.ECase (cs, o)))]

        | Syntax.EWithState ss -> genCoreStatements fresh env ss

        | Syntax.ETags _ -> []

        | Syntax.EIdentifier id ->
            match id.Name.Kind with
            | Syntax.NameKind.ISmall ->
                if Map.containsKey id.Name.Name env
                then
                    if env.[id.Name.Name].Empty
                    then []
                    elif env.[id.Name.Name].Native
                    then [WNativeVar id.Name.Name]
                    elif env.[id.Name.Name].Callable
                    then [WCallVar id.Name.Name]
                    else [WValueVar id.Name.Name]
                else
                    failwith $"Name '{id.Name.Name}' not found during CoreGen."
            | Syntax.NameKind.IBig -> [WConstructorVar id.Name.Name]
            | Syntax.NameKind.IOperator -> [WOperatorVar id.Name.Name]
            | Syntax.NameKind.IPredicate -> [WTestConstructorVar id.Name.Name]
        | Syntax.ERecursivePlaceholder (n, _) -> failwith $"CoreGen: Recursive placeholder for {n} not erased during elaboration!"
        | Syntax.EMethodPlaceholder (m, t) -> failwith $"CoreGen: Method placeholder for {m} : {t} not erased during elaboration!"
        | Syntax.EOverloadPlaceholder _ -> failwith "CoreGen: Overload placeholder not erased during elaboration!"

        | Syntax.EDo -> [WDo]
        | Syntax.EInteger id -> [WInteger (id.Value, id.Size)]
        | Syntax.EDecimal id -> [WDecimal (id.Value, id.Size)]
        | Syntax.EString id -> [WString id.Value]
        | Syntax.ECharacter c -> [WChar (c.Value.Chars 1)]
        | Syntax.ETrue -> [primTrueBool]
        | Syntax.EFalse -> [primFalseBool]
    and genCoreStatements fresh env stmts =
        match stmts with
        | [] -> []
        | s :: ss ->
            match s with
            | Syntax.SLet clause ->
                let ce = genCoreExpr fresh env clause.Body
                let cbs = genCoreWord fresh env (Syntax.EMatch ([{ clause with Body = [Syntax.EStatementBlock ss] }], []))
                List.append ce cbs
            | Syntax.SLocals locals ->
                failwith "Local compilation not yet implemented."
            | Syntax.SExpression e -> List.append (genCoreExpr fresh env e) (genCoreStatements fresh env ss)
    and genHandler fresh env hdlr =
        let pars = [for p in hdlr.Params -> p.Name]
        let envWithParams = List.fold (fun e p -> Map.add p varEntry e) env pars
        let handlerEnv = Map.add "resume" { Callable = true; Native = false; Empty = false } envWithParams
        {
            Name = hdlr.Name.Name.Name;
            Params = pars;
            Body = genCoreExpr fresh handlerEnv hdlr.Body
        }
    and genSingleMatch fresh env clause other =
        match Syntax.getFlatVars clause.Matcher with
        | Some vars ->
            let matchEnv = [for v in vars -> (v, varEntry)] |> Map.ofList |> mapUnion fst env
            [WVars (vars, genCoreExpr fresh matchEnv clause.Body)]
        | None ->
            genHandlePatternMatches fresh env [clause] other
    and genCoreForEffect fresh env assign body =
        match assign with
        | [] -> genCoreStatements fresh env body
        | iter :: iters ->
            let subEnv =
                Map.add iter.Name.Name varEntry env
                |> Map.add "resume" { Callable = true; Native = false; Empty = false }
            match iter.SeqType with
            | Syntax.FForIterator ->
                [WHandle (
                    [],
                    genCoreExpr fresh env iter.Assigned,
                    [{
                        Name = "yield!";
                        Params = [iter.Name.Name];
                        Body = List.append (genCoreForEffect fresh subEnv iters body) [WCallVar "resume"]
                    }],
                    ([],[]))]
            | _ -> 
                let whileCheck = genAssignCheck fresh env iter
                let whileBody =
                    List.append
                        (genAssignElement fresh env iter)
                        [WVars (
                            [iter.Name.Name],
                            List.append (genCoreForEffect fresh subEnv iters body) (genOverwriteAssign fresh env iter))]
                List.append
                    (genCoreExpr fresh env iter.Assigned)
                    [WVars ([iter.Name.Name + "-iter*"], [WWhile (whileCheck, whileBody)])]
    and genCoreForComp fresh env res accNames assign body =
        match res with
        | [] -> 
            match assign with
            | [] ->
                List.append
                    (genCoreStatements fresh env body)
                    (List.concat [for a in List.rev accNames -> genForMapAcc fresh env a])
            | iter :: iters ->
                let subEnv =
                    Map.add iter.Name.Name varEntry env
                    |> Map.add "resume" { Callable = true; Native = false; Empty = false }
                match iter.SeqType with
                | Syntax.FForIterator ->
                    List.append
                        [for a in List.rev accNames do if snd a <> Syntax.FForIterator then WValueVar (fst a)]
                        [WHandle (
                            [for a in List.rev accNames do if snd a <> Syntax.FForIterator then (fst a)],
                            genCoreExpr fresh env iter.Assigned,
                            [{
                                Name = "yield!";
                                Params = [iter.Name.Name];
                                Body = List.append (genCoreForComp fresh subEnv [] accNames iters body) [WCallVar "resume"]
                            }],
                            ([], [for a in List.rev accNames do if snd a <> Syntax.FForIterator then WValueVar (fst a)])
                        )]
                | _ ->
                    let whileCheck = genAssignCheck fresh env iter
                    let whileBody =
                        List.append
                            (genAssignElement fresh env iter)
                            [WVars (
                                [iter.Name.Name],
                                append3
                                    (genCoreForComp fresh subEnv [] accNames iters body)
                                    [for r in List.rev accNames do if snd r <> Syntax.FForIterator then WOverwriteValueVar (fst r)]
                                    (genOverwriteAssign fresh env iter))]
                    List.append
                        (genCoreExpr fresh env iter.Assigned)
                        [WVars ([iter.Name.Name + "-iter*"], WWhile (whileCheck, whileBody) :: [for a in List.rev accNames do if snd a <> Syntax.FForIterator then WValueVar (fst a)])]
        | (n, r) :: res ->
            let wrapSub =
                match r with
                | Syntax.FForIterator -> genCoreForComp fresh env res accNames assign body
                | _ -> [WVars ([n], genCoreForComp fresh env res accNames assign body)]
            List.append (genForMapInit fresh env r) wrapSub
    and genCoreForFold fresh env accs accNames assign body =
        match accs with
        | [] ->
            match assign with
            | [] -> genCoreStatements fresh env body
            | iter :: iters ->
                let subEnv =
                    Map.add iter.Name.Name varEntry env
                    |> Map.add "resume" { Callable = true; Native = false; Empty = false }
                match iter.SeqType with
                | Syntax.FForIterator ->
                    List.append
                        [for a in accNames -> WValueVar a]
                        [WHandle (
                            [for a in accNames -> a],
                            genCoreExpr fresh env iter.Assigned,
                            [{
                                Name = "yield!";
                                Params = [iter.Name.Name];
                                Body = List.append (genCoreForFold fresh subEnv [] accNames iters body) [WCallVar "resume"]
                            }],
                            ([], [for a in accNames -> WValueVar a]))]
                | _ -> 
                    let whileCheck = genAssignCheck fresh env iter
                    let whileBody =
                        List.append
                            (genAssignElement fresh env iter)
                            [WVars (
                                [iter.Name.Name],
                                append3
                                    (genCoreForFold fresh subEnv [] accNames iters body)
                                    [for a in accNames -> WOverwriteValueVar a]
                                    (genOverwriteAssign fresh env iter))]
                    List.append
                        (genCoreExpr fresh env iter.Assigned)
                        [WVars ([iter.Name.Name + "-iter*"], WWhile (whileCheck, whileBody) :: [for a in accNames -> WValueVar a])]
        | acc :: accs ->
            let subEnv = Map.add acc.Name.Name varEntry env
            List.append
                (genCoreExpr fresh env acc.Assigned)
                [WVars ([acc.Name.Name],
                    genCoreForFold fresh subEnv accs accNames assign body)]
    and genAssignCheck fresh env assign =
        match assign.SeqType with
        | Syntax.FForTuple ->
            [WValueVar (assign.Name.Name + "-iter*"); primLengthTuple; WInteger ("0", Types.INative); primGreaterINative]
        | Syntax.FForList ->
            [WValueVar (assign.Name.Name + "-iter*"); primLengthList; WInteger ("0", Types.INative); primGreaterINative]
        | Syntax.FForString ->
            [WValueVar (assign.Name.Name + "-iter*"); primLengthString; WInteger ("0", Types.INative); primGreaterINative]
        | _ -> failwith $"For assignment check not implemented for sequence type {assign.SeqType}"
    and genAssignElement fresh env assign =
        match assign.SeqType with
        | Syntax.FForTuple ->
            [WValueVar (assign.Name.Name + "-iter*"); primHeadTuple]
        | Syntax.FForList ->
            [WValueVar (assign.Name.Name + "-iter*"); primHeadList]
        | Syntax.FForString ->
            [WValueVar (assign.Name.Name + "-iter*"); primHeadString]
        | _ -> failwith $"For assignment check not implemented for sequence type {assign.SeqType}"
    and genOverwriteAssign fresh env assign =
        match assign.SeqType with
        | Syntax.FForTuple ->
            [WValueVar (assign.Name.Name + "-iter*"); primTailTuple; WOverwriteValueVar (assign.Name.Name + "-iter*")]
        | Syntax.FForList ->
            [WValueVar (assign.Name.Name + "-iter*"); primTailList; WOverwriteValueVar (assign.Name.Name + "-iter*")]
        | Syntax.FForString ->
            [WValueVar (assign.Name.Name + "-iter*"); primTailString; WOverwriteValueVar (assign.Name.Name + "-iter*")]
        | _ -> failwith $"For assignment overwrite not implemented for sequence type {assign.SeqType}"
    and genForMapInit fresh env resType =
        match resType with
        | Syntax.FForTuple -> [primNilTuple]
        | Syntax.FForList -> [primNilList]
        | Syntax.FForString -> [primNilString]
        | Syntax.FForIterator -> []
        | _ -> failwith $"For map init not implemented for sequence type {resType}"
    and genForMapAcc fresh env (name, resType) =
        match resType with
        | Syntax.FForTuple ->
            [WValueVar name; primSwap; primConsTuple]
        | Syntax.FForList ->
            [WValueVar name; primSwap; primSnocList]
        | Syntax.FForString ->
            [WValueVar name; primSwap; primSnocString]
        | Syntax.FForIterator ->
            [primYield]
        | _ -> failwith $"For map accumulate not implemented for sequence type {resType}"
    and genCoreExpr fresh env expr =
        List.collect (genCoreWord fresh env) expr

    and genHandlePatternMatches (fresh: FreshVars) env clauses otherwise =
        // TODO: this does not support dotted patterns yet
        let vars = fresh.FreshN "$mat" (DotSeq.length (clauses.[0].Matcher))
        let placeVars = List.map WValueVar vars
        let genClauses = [for i, c in List.mapi (fun i c -> (i, c)) clauses -> genPatternMatchClause fresh env i c]
        [WVars (vars,
            [WHandle (
                [],
                List.append
                    (List.concat [for i in 0..List.length clauses-1 -> List.append placeVars [WOperatorVar $"$match{i}!"]])
                    (List.append placeVars [WOperatorVar "$default!"]),
                genPatternOtherwise fresh env (DotSeq.length (clauses.[0].Matcher)) otherwise :: genClauses,
                ([],[]))])]
    and genPatternMatchClause fresh env ind clause =
        let patVars = fresh.FreshN "$pat" (DotSeq.length clause.Matcher)
        let placePat = List.map WValueVar patVars
        let checkMatch = genCheckPatterns fresh env (DotSeq.rev clause.Matcher) clause.Body
        { Name = $"$match{ind}!"; Params = patVars; Body = List.append placePat checkMatch }
    and genPatternOtherwise fresh env paramCount expr =
        let patVars = fresh.FreshN "$pat" paramCount
        let placePat = List.map WValueVar patVars
        { Name = "$default!"; Params = patVars; Body = List.append placePat expr }
    and genCheckPatterns fresh env patterns body =
        match patterns with
        | DotSeq.SEnd -> genCoreExpr fresh env body
        | DotSeq.SDot (v, DotSeq.SEnd) when Syntax.isAnyMatchPattern v ->
            let free = Syntax.patternNames v |> Syntax.namesToStrings |> Seq.toList
            let inner = genCoreExpr fresh env body
            if List.isEmpty free
            then inner
            else [WVars ([free.[0]], inner)]
        | DotSeq.SDot _ ->
            failwith "Found a dotted pattern in non-end position, this is invalid."
        | DotSeq.SInd (p, ps) ->
            let free = Syntax.patternNames p |> Syntax.namesToStrings |> Seq.toList
            let namedEnv = List.fold (fun e n -> Map.add n varEntry e) env free
            let inner = genCheckPatterns fresh namedEnv ps body
            genCheckPattern fresh env inner p
    and genCheckPattern fresh env inner pattern =
        // note that environment extension of variables in patterns is handled outside of this method
        let resume = [WCallVar "resume"]
        match pattern with
        | Syntax.PTrue -> [WIf (inner, resume)]
        | Syntax.PFalse -> [primNotBool; WIf (inner, resume)]
        | Syntax.PString s -> [WString s.Value; primEqString; WIf (inner, resume)]
        | Syntax.PInteger i -> [WInteger (i.Value, i.Size); intEqs.[i.Size]; WIf (inner, resume)]
        | Syntax.PDecimal f -> [WDecimal (f.Value, f.Size); floatEqs.[f.Size]; WIf (inner, resume)]
        | Syntax.PWildcard -> primDrop :: inner
        | Syntax.PRef p -> primRefGet :: genCheckPattern fresh env inner p
        | Syntax.PNamed (n, Syntax.PWildcard) ->
            [WVars ([n.Name], inner)]
        | Syntax.PNamed (n, p) ->
            [primDup; WVars ([n.Name], genCheckPattern fresh env inner p)]
        | Syntax.PConstructor (id, ps) ->
            [primDup;
             WTestConstructorVar id.Name.Name;
             WIf (
                WDestruct :: DotSeq.foldBack (fun p st -> genCheckPattern fresh env st p) inner ps,
                resume)]
        | Syntax.PTuple DotSeq.SEnd -> primDrop :: inner
        | Syntax.PTuple (DotSeq.SDot (v, DotSeq.SEnd)) when Syntax.isAnyMatchPattern v ->
            let free = Syntax.patternNames v |> Syntax.namesToStrings |> Seq.toList
            if List.isEmpty free
            then primDrop :: inner
            else [WVars ([free.[0]], inner)]
        | Syntax.PTuple (DotSeq.SDot _) -> failwith "Invalid dot-pattern in tuple."
        | Syntax.PTuple (DotSeq.SInd (p, ps)) ->
            primBreakTuple :: genCheckPattern fresh env (genCheckPattern fresh env inner (Syntax.PTuple ps)) p
        | Syntax.PList DotSeq.SEnd ->
            [primDup; primIsEmptyList;
             WIf (primDrop :: inner, primDrop :: resume)]
        | Syntax.PList (DotSeq.SDot (v, DotSeq.SEnd)) when Syntax.isAnyMatchPattern v ->
            let free = Syntax.patternNames v |> Syntax.namesToStrings |> Seq.toList
            if List.isEmpty free
            then primDrop :: inner
            else [WVars ([free.[0]], inner)]
        | Syntax.PList (DotSeq.SDot _) -> failwith "Invalid dot-pattern in list."
        | Syntax.PList (DotSeq.SInd (p, ps)) ->
            [primDup; primIsEmptyList; primNotBool;
             WIf (
                primBreakList :: genCheckPattern fresh env (genCheckPattern fresh env inner (Syntax.PList ps)) p,
                primDrop :: resume)]
        | Syntax.PRecord [] -> primDrop :: inner
        | Syntax.PRecord (f :: fs) ->
            let checkRest = genCheckPattern fresh env inner (Syntax.PRecord fs)
            let checkFst = genCheckPattern fresh env checkRest (snd f)
            List.append [primDup; WSelect (fst f).Name] checkFst
        | p -> failwith $"Pattern {p} not yet supported for pattern matching compilation."

    let nativeEntries (nat: Condenser.Native) = [for d in nat.Decls -> (d.Name.Name, natEntry)]

    let genCoreProgram (program : CondensedProgram) =
        let fresh = SimpleFresh(0)
        let ctors = List.mapi (fun id (c: Syntax.Constructor) -> (c.Name.Name, { Id = id; Args = List.length c.Components })) program.Constructors |> Map.ofList
        let env = List.map (fun (c, b) -> (c, { Callable = true; Native = false; Empty = List.isEmpty b })) program.Definitions |> Map.ofList
        let natEntries = List.collect nativeEntries program.Natives
        let env = mapUnion snd (Map.ofList natEntries) env
        let defs =
            List.filter (snd >> List.isEmpty >> not) program.Definitions |>
            List.map (fun (c, body) -> 
                try
                    (c, genCoreExpr fresh env body)
                with
                    ex -> failwith $"Core generation of '{c}' failed with {ex}")
            |> Map.ofList
        let hdlrs =
            program.Effects
            |> List.mapi (fun idx e ->
                e.Handlers
                |> List.mapi (fun hidx h -> (h.Name, { HandleId = idx; HandlerIndex = hidx; Inputs = h.Inputs; Outputs = h.Outputs }))
                |> Map.ofList)
            |> List.fold (mapUnion fst) Map.empty
        let effs =
            program.Effects
            |> List.mapi (fun idx e -> (e.Name, idx))
            |> Map.ofList
        let nats = [
            for n in program.Natives ->
            { UnitName = n.UnitName;
              Imports = n.Imports;
              Decls = [for d in n.Decls -> (d.Name.Name, d.Lines)] |> Map.ofList }]
        { Main = 
            try
                genCoreExpr fresh env program.Main
            with
                ex -> failwith $"Core generation of 'main' failed with {ex}";
          Constructors = ctors;
          Definitions = defs;
          Handlers = hdlrs;
          Effects = effs;
          Natives = nats;
          BlockId = ref 0 }