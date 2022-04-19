namespace Boba.Compiler

module CoreGen =

    open System
    open Boba.Core
    open Boba.Core.Common
    open Boba.Core.Fresh
    open Boba.Core.Syntax
    open Boba.Compiler.Condenser

    type EnvEntry = {
        Callable: bool;
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

    type TopLevelProg = {
        Main: Expression;
        Definitions: Map<string, Expression>;
        Constructors: Map<string, Constructor>;
        Handlers: Map<string, HandlerMeta>;
        Effects: Map<string, int>;
        BlockId: ref<int>;
    }

    let varEntry = { Callable = false; Empty = false }

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
            //else genPatternMatches fresh env cs genO
        | Syntax.EIf (c, t, e) ->
            let cg = genCoreExpr fresh env c
            let tg = genCoreStatements fresh env t
            let eg = genCoreStatements fresh env e
            List.append cg [WIf (tg, eg)]
        | Syntax.EWhile (c, b) ->
            let cg = genCoreExpr fresh env c
            let bg = genCoreStatements fresh env b
            [WWhile (cg, bg)]

        | Syntax.EFunctionLiteral e -> [WFunctionLiteral (genCoreExpr fresh env e)]
        | Syntax.ETupleLiteral [] -> [WPrimVar "nil-tuple"]
        // TODO: tuple literals with a splat expression may need some adjustment here, to support
        // splatting in the main expression if we want
        | Syntax.ETupleLiteral exp -> genCoreExpr fresh env exp
        | Syntax.EListLiteral (r, es) ->
            let esg = List.collect (genCoreExpr fresh env) es
            let consg = List.collect (fun _ -> [WPrimVar "list-cons"]) es
            if List.isEmpty r
            then List.concat [esg; [WPrimVar "list-nil"]; consg]
            else List.concat [esg; genCoreExpr fresh env r; consg]

        | Syntax.ERecordLiteral [] -> [WEmptyRecord]
        | Syntax.ERecordLiteral exp -> genCoreExpr fresh env exp
        | Syntax.EExtension n -> [WExtension n.Name]
        | Syntax.ESelect (true, n) -> [WSelect n.Name]
        | Syntax.ESelect (false, n) -> [WPrimVar "dup"; WSelect n.Name]

        | Syntax.EVariantLiteral (n, exp) -> List.append (genCoreExpr fresh env exp) [WVariantLiteral n.Name]
        | Syntax.ECase ([], _) -> failwith "Improper case statement encountered during core code generation."
        | Syntax.ECase ([c], o) -> [WCase (c.Tag.Name, genCoreExpr fresh env c.Body, genCoreExpr fresh env o)]
        | Syntax.ECase (c :: cs, o) -> [WCase (c.Tag.Name, genCoreExpr fresh env c.Body, genCoreWord fresh env (Syntax.ECase (cs, o)))]

        | Syntax.EWithState ss -> genCoreStatements fresh env ss
        | Syntax.ENewRef -> [WPrimVar "new-ref"]
        | Syntax.EGetRef -> [WPrimVar "get-ref"]
        | Syntax.EPutRef -> [WPrimVar "put-ref"]

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
                    elif env.[id.Name.Name].Callable
                    then [WCallVar id.Name.Name]
                    else [WValueVar id.Name.Name]
                else
                    [WPrimVar id.Name.Name]
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
                elif env.[id].Callable
                then [WCallVar id]
                else [WValueVar id]
            else
                [WPrimVar id]

        | Syntax.EDo -> [WDo]
        | Syntax.EInteger id -> [WInteger (id.Value, id.Size)]
        | Syntax.EDecimal id -> [WDecimal (id.Value, id.Size)]
        | Syntax.EString id -> [WString id.Value]
        | Syntax.ETrue -> [WPrimVar "bool-true"]
        | Syntax.EFalse -> [WPrimVar "bool-false"]
        | other -> failwith $"Unimplemented generation for {other}"
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
        let pars = List.map (fun (p : Syntax.Name) -> p.Name) hdlr.Params
        let envWithParams = List.fold (fun e p -> Map.add p varEntry e) env pars
        let handlerEnv = Map.add "resume" { Callable = true; Empty = false } envWithParams
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
    and genCoreExpr fresh env expr =
        List.collect (genCoreWord fresh env) expr

    and genHandlePatternMatches (fresh: FreshVars) env clauses otherwise =
        let vars = fresh.FreshN "$mat" (DotSeq.length (clauses.[0].Matcher))
        let placeVars = List.map WValueVar vars
        [WVars (vars,
            [WHandle (
                [],
                List.append
                    (List.concat [for i in 0..List.length clauses -> List.append placeVars [WOperatorVar $"$match{i}!"]])
                    (List.append (if otherwise.Length <> 0 then placeVars else []) [WOperatorVar "$default!"]),
                List.append
                    [for i, c in List.mapi (fun i c -> (i, c)) clauses -> genPatternMatchClause fresh env i c]
                    [{ Name = "$default!"; Params = []; Body = otherwise }],
                [])])]
    and genPatternMatchClause fresh env ind clause =
        let patVars = fresh.FreshN "$pat" (DotSeq.length clause.Matcher)
        let placePat = List.map WValueVar patVars
        let checkMatch = genCheckPatterns fresh env clause.Matcher clause.Body
        { Name = $"$match{ind}!"; Params = patVars; Body = List.append placePat checkMatch }
    and genCheckPatterns fresh env patterns body =
        match patterns with
        | DotSeq.SEnd -> genCoreExpr fresh env body
        | DotSeq.SDot (v, DotSeq.SEnd) ->
            failwith "Dotted top-level patterns not yet supported."
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
        | Syntax.PFalse -> [WPrimVar "not-bool"; WIf (inner, resume)]
        | Syntax.PString s -> [WString s.Value; WPrimVar "eq-string"; WIf (inner, resume)]
        // TODO: support various sizes of integers in patterns
        | Syntax.PInteger i -> [WInteger (i.Value, i.Size); WPrimVar "eq-i32"; WIf (inner, resume)]
        // TODO: support various sizes of floats in patterns
        | Syntax.PDecimal f -> [WDecimal (f.Value, f.Size); WPrimVar "eq-single"; WIf (inner, resume)]
        | Syntax.PWildcard -> inner
        | Syntax.PRef p -> WPrimVar "get-ref" :: genCheckPattern fresh env inner p
        | Syntax.PNamed (n, p) ->
            [WPrimVar "dup"; WVars ([n.Name], genCheckPattern fresh env inner p)]
        | Syntax.PConstructor (id, ps) ->
            [WPrimVar "dup";
             WTestConstructorVar id.Name.Name;
             WIf (
                WDestruct :: DotSeq.fold (fun st p -> List.append st (genCheckPattern fresh env inner p)) [] ps,
                resume)]
        | Syntax.PTuple DotSeq.SEnd -> WPrimVar "drop" :: inner
        | Syntax.PTuple (DotSeq.SDot (v, DotSeq.SEnd)) when Syntax.isAnyMatchPattern v ->
            let free = Syntax.patternNames v |> Syntax.namesToStrings |> Seq.toList
            if List.isEmpty free
            then WPrimVar "drop" :: inner
            else [WVars ([free.[0]], inner)]
        | Syntax.PTuple (DotSeq.SDot _) -> failwith "Invalid dot-pattern in tuple."
        | Syntax.PTuple (DotSeq.SInd (p, ps)) ->
            WPrimVar "break-tuple" :: genCheckPattern fresh env (genCheckPattern fresh env inner (Syntax.PTuple ps)) p
        | p -> failwith $"Pattern {p} not yet supported for pattern matching compilation."

    let genCoreProgram (program : CondensedProgram) =
        let fresh = SimpleFresh(0)
        let ctors = List.mapi (fun id (c: Syntax.Constructor) -> (c.Name.Name, { Id = id; Args = List.length c.Components })) program.Constructors |> Map.ofList
        let env = List.map (fun (c, b) -> (c, { Callable = true; Empty = List.isEmpty b })) program.Definitions |> Map.ofList
        let defs =
            List.filter (snd >> List.isEmpty >> not) program.Definitions |>
            List.map (fun (c, body) -> (c, genCoreExpr fresh env body))
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
        { Main = genCoreExpr fresh env program.Main;
          Constructors = ctors;
          Definitions = defs;
          Handlers = hdlrs;
          Effects = effs;
          BlockId = ref 0 }