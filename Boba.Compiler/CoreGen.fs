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
        | Syntax.EHandle (ps, h, hs, r) ->
            let hg = genCoreStatements fresh env h
            let pars = List.map (fun (id : Syntax.Name) -> id.Name) ps
            let hEnv = List.fold (fun e n -> Map.add n varEntry e) env pars
            let hgs = List.map (genHandler fresh hEnv) hs
            let rg = genCoreExpr fresh hEnv r
            [WHandle (pars, hg, hgs, rg)]
        | Syntax.EInject (ns, ss) ->
            let effs = List.map (fun (id : Syntax.Name) -> id.Name) ns
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
        | Syntax.EForEffect (assign, body) -> genCoreForEffect fresh env assign body
        | Syntax.EForComprehension (res, assign, body) -> genCoreForComprehension fresh env res assign body
        | Syntax.EForFold (accs, assign, body) ->
            if List.exists (fun (a : Syntax.ForAssignClause) -> a.SeqType = Syntax.FForIterator) assign
            then genCoreForFoldIterator fresh env accs assign body
            else genCoreForFold fresh env accs assign body

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

        | Syntax.EUntag _ -> []
        | Syntax.EBy _ -> []
        | Syntax.EPer _ -> []
        | Syntax.ETrust -> []
        | Syntax.EDistrust -> []
        | Syntax.EAudit -> []

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
        | Syntax.ERecursivePlaceholder (id, ty) ->
            // TODO: THIS IS NOT VALID, NEED TO EXPAND TYPE CLASS METHODS AFTER INFERENCE
            // VERY TEMPORARY TO MAKE RECURSIVE FUNCTIONS COMPILE FOR NOW
            if Map.containsKey id env
            then
                if env.[id].Empty
                then []
                elif env.[id].Native
                then [WNativeVar id]
                elif env.[id].Callable
                then [WCallVar id]
                else [WValueVar id]
            else
                failwith $"Name '{id}' not found in environment during CoreGen."
        | Syntax.EMethodPlaceholder (m, t) -> failwith $"CoreGen: Method placeholder for {m} : {t} not erased during elaboration!"
        | Syntax.EOverloadPlaceholder _ -> failwith "CoreGen: Overload placeholder not erased during elaboration!"

        | Syntax.EDo -> [WDo]
        | Syntax.EInteger id -> [WInteger (id.Value, id.Size)]
        | Syntax.EDecimal id -> [WDecimal (id.Value, id.Size)]
        | Syntax.EString id -> [WString id.Value]
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
        let assignNames = [for a in assign -> (a.Name.Name, varEntry)]
        let bodyEnv = assignNames |> Map.ofList |> mapUnion fst env
        let genBody = genCoreStatements fresh bodyEnv body
        let whileCheck =
            List.append
                (List.concat [for a in assign -> genAssignCheck fresh env a])
                [for _ in assign.Tail -> primAndBool]
        let whileBody =
            List.append
                (List.concat [for a in assign -> genAssignElement fresh env a])
                [WVars (
                    List.map fst assignNames,
                    List.append genBody (List.concat [for a in assign -> genOverwriteAssign fresh env a]))]
        [WVars (List.map (fun n -> fst n + "-iter*") assignNames, [WWhile (whileCheck, whileBody)])]
    and genCoreForComprehension fresh env res assign body =
        let nonIterRes = List.filter (fun r -> r <> Syntax.FForIterator) res
        let accNames = [for r in res -> (r = Syntax.FForIterator, (fresh.Fresh "$mapRes", varEntry))]
        let allAccNames = List.map snd accNames
        let nonIterAccNames = List.filter (fun (iter, _) -> not iter) accNames |> List.map snd
        let assignNames = [for a in assign -> (a.Name.Name, varEntry)]
        let bodyEnv = List.append allAccNames assignNames |> Map.ofList |> mapUnion fst env
        let genBody = genCoreStatements fresh bodyEnv body
        let foldInits = List.concat [for r in nonIterRes -> genForMapInit fresh env r]
        let whileCheck =
            List.append
                (List.concat [for a in assign -> genAssignCheck fresh env a])
                [for _ in assign.Tail -> primAndBool]
        let whileBody =
            List.append
                // push assign elements every iteration of the loop
                (List.concat [for a in assign -> genAssignElement fresh env a])
                [WVars (
                    List.map fst assignNames,
                    append3
                        genBody
                        // results of the body expression get assigned back to the init vars
                        (List.concat [for r in List.rev (List.zip allAccNames res) -> genForMapAcc fresh env r])
                        // move forward in the iteration
                        (List.concat [for a in assign -> genOverwriteAssign fresh env a]))]
        append3
            (List.concat [for a in assign -> genCoreExpr fresh env a.Assigned])
            foldInits
            [WVars ([for a in nonIterAccNames -> fst a],
                [WVars (List.map (fun n -> fst n + "-iter*") assignNames,
                    WWhile (whileCheck, whileBody) :: [for a in nonIterAccNames -> WValueVar (fst a)])])]
    and genCoreForFoldIterator fresh env accs assign body =
        if List.length assign > 1
        then failwith $"Only one assign clause currently supported in for-loops over iterators."
        let foldInits = List.concat [for a in accs -> genCoreExpr fresh env a.Assigned]
        let bodyEnv =
            List.append [for a in accs -> (a.Name.Name, varEntry)] [for a in assign -> (a.Name.Name, varEntry)]
            |> Map.ofList
            |> mapUnion snd env
        let handlerEnv = Map.add "resume" { Callable = true; Native = false; Empty = false } bodyEnv
        List.append
            foldInits
            [WVars (
                [for a in accs -> a.Name.Name],
                [primGather;
                 WVars (
                    ["$saved"],
                    List.append
                        [for a in accs -> WValueVar a.Name.Name]
                        [WHandle (
                            [for a in accs -> a.Name.Name],
                            List.concat [for a in assign -> genCoreExpr fresh env a.Assigned],
                            [{
                                Name = "yield!";
                                Params = [for a in assign -> a.Name.Name];
                                Body = List.append (genCoreStatements fresh handlerEnv body) [WCallVar "resume"]
                            }],
                            [for a in accs -> WValueVar (a.Name.Name)]);
                         WValueVar "$saved";
                         primSpread])])]
    and genCoreForFold fresh env accs assign body =
        let accNames = [for a in accs -> (a.Name.Name, varEntry)]
        let assignNames = [for a in assign -> (a.Name.Name, varEntry)]
        let bodyEnv = List.append accNames assignNames |> Map.ofList |> mapUnion snd env
        let genBody = genCoreStatements fresh bodyEnv body
        let foldInits = List.concat [for a in accs -> genCoreExpr fresh env a.Assigned]
        let whileCheck =
            List.append
                (List.concat [for a in assign -> genAssignCheck fresh env a])
                [for _ in assign.Tail -> primAndBool]
        let whileBody =
            List.append
                // push assign elements every iteration of the loop
                (List.concat [for a in assign -> genAssignElement fresh env a])
                [WVars (
                    List.map fst assignNames,
                    append3
                        genBody
                        // results of the body expression get assigned back to the init vars
                        (List.concat [for a in accs -> [WOverwriteValueVar a.Name.Name]])
                        // move forward in the iteration
                        (List.concat [for a in assign -> genOverwriteAssign fresh env a]))]
        append3
            (List.concat [for a in assign -> genCoreExpr fresh env a.Assigned])
            foldInits
            [WVars ([for a in accs -> a.Name.Name],
                [WVars (List.map (fun n -> fst n + "-iter*") assignNames,
                    WWhile (whileCheck, whileBody) :: [for a in accs -> WValueVar a.Name.Name])])]
    and genAssignCheck fresh env assign =
        match assign.SeqType with
        | Syntax.FForTuple ->
            [WValueVar (assign.Name.Name + "-iter*"); primLengthTuple; WInteger ("0", Types.I32); primGreaterI32]
        | Syntax.FForList ->
            [WValueVar (assign.Name.Name + "-iter*"); primLengthList; WInteger ("0", Types.I32); primGreaterI32]
        | _ -> failwith $"For assignment check not implemented for sequence type {assign.SeqType}"
    and genAssignElement fresh env assign =
        match assign.SeqType with
        | Syntax.FForTuple ->
            [WValueVar (assign.Name.Name + "-iter*"); primHeadTuple]
        | Syntax.FForList ->
            [WValueVar (assign.Name.Name + "-iter*"); primHeadList]
        | _ -> failwith $"For assignment check not implemented for sequence type {assign.SeqType}"
    and genOverwriteAssign fresh env assign =
        match assign.SeqType with
        | Syntax.FForTuple ->
            [WValueVar (assign.Name.Name + "-iter*"); primTailTuple; WOverwriteValueVar (assign.Name.Name + "-iter*")]
        | Syntax.FForList ->
            [WValueVar (assign.Name.Name + "-iter*"); primTailList; WOverwriteValueVar (assign.Name.Name + "-iter*")]
        | _ -> failwith $"For assignment overwrite not implemented for sequence type {assign.SeqType}"
    and genForMapInit fresh env resType =
        match resType with
        | Syntax.FForTuple -> [primNilTuple]
        | Syntax.FForList -> [primNilList]
        | Syntax.FForIterator -> []
        | _ -> failwith $"For map init not implemented for sequence type {resType}"
    and genForMapAcc fresh env ((name, _), resType) =
        match resType with
        | Syntax.FForTuple ->
            [WValueVar name; primSwap; primConsTuple; WOverwriteValueVar name]
        | Syntax.FForList ->
            [WValueVar name; primSwap; primConsList; WOverwriteValueVar name]
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
            [primGather;
             WVars (["$saved"],
                [WHandle (
                    [],
                    List.append
                        (List.concat [for i in 0..List.length clauses -> List.append placeVars [WOperatorVar $"$match{i}!"]])
                        (List.append placeVars [WOperatorVar "$default!"]),
                    { Name = "$default!"; Params = []; Body = otherwise } :: genClauses,
                    []);
                 WValueVar "$saved";
                 primSpread])])]
    and genPatternMatchClause fresh env ind clause =
        let patVars = fresh.FreshN "$pat" (DotSeq.length clause.Matcher)
        let placePat = List.map WValueVar patVars
        let checkMatch = genCheckPatterns fresh env clause.Matcher clause.Body
        { Name = $"$match{ind}!"; Params = patVars; Body = List.append placePat checkMatch }
    and genCheckPatterns fresh env patterns body =
        match patterns with
        | DotSeq.SEnd -> genCoreExpr fresh env body
        | DotSeq.SDot (v, DotSeq.SEnd) when Syntax.isAnyMatchPattern v ->
            let free = Syntax.patternNames v |> Syntax.namesToStrings |> Seq.toList
            let inner = genCoreExpr fresh env body
            if List.isEmpty free
            then primClear :: inner
            else [primGather; WVars ([free.[0]], inner)]
        | DotSeq.SDot _ ->
            failwith "Found a dotted pattern in non-end position, this is invalid."
        | DotSeq.SInd (p, ps) ->
            let free = Syntax.patternNames p |> Syntax.namesToStrings |> Seq.toList
            let namedEnv = List.fold (fun e n -> Map.add n varEntry e) env free
            let inner = genCheckPatterns fresh namedEnv ps body
            genCheckPattern fresh env inner p
    and genCheckPattern fresh env inner pattern =
        // note that environment extension of variables in patterns is handled outside of this method
        let resume = [primClear; WCallVar "resume"]
        match pattern with
        | Syntax.PTrue -> [WIf (inner, resume)]
        | Syntax.PFalse -> [primNotBool; WIf (inner, resume)]
        | Syntax.PString s -> [WString s.Value; primEqString; WIf (inner, resume)]
        // TODO: support various sizes of integers in patterns
        | Syntax.PInteger i -> [WInteger (i.Value, i.Size); primEqI32; WIf (inner, resume)]
        // TODO: support various sizes of floats in patterns
        | Syntax.PDecimal f -> [WDecimal (f.Value, f.Size); primEqSingle; WIf (inner, resume)]
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
            [primIsEmptyList;
             WIf (primDrop :: inner, resume)]
        | Syntax.PList (DotSeq.SDot (v, DotSeq.SEnd)) when Syntax.isAnyMatchPattern v ->
            let free = Syntax.patternNames v |> Syntax.namesToStrings |> Seq.toList
            if List.isEmpty free
            then primDrop :: inner
            else [WVars ([free.[0]], inner)]
        | Syntax.PList (DotSeq.SDot _) -> failwith "Invalid dot-pattern in list."
        | Syntax.PList (DotSeq.SInd (p, ps)) ->
            [primIsEmptyList; primNotBool;
             WIf (
                primBreakList :: genCheckPattern fresh env (genCheckPattern fresh env inner (Syntax.PList ps)) p,
                resume)]
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
                |> List.mapi (fun hidx h -> (h, { HandleId = idx; HandlerIndex = hidx }))
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