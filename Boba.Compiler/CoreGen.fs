namespace Boba.Compiler

module CoreGen =

    open System
    open Boba.Core
    open Boba.Core.Common
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

    let rec genCoreWord env word =
        match word with
        | Syntax.EStatementBlock ss -> genCoreStatements env ss
        | Syntax.EHandle (ps, h, hs, r) ->
            let hg = genCoreStatements env h
            let pars = List.map (fun (id : Syntax.Name) -> id.Name) ps
            let hEnv = List.fold (fun e n -> Map.add n varEntry e) env pars
            let hgs = List.map (genHandler hEnv) hs
            let rg = genCoreExpr hEnv r
            [WHandle (pars, hg, hgs, rg)]
        | Syntax.EInject (ns, ss) ->
            let effs = List.map (fun (id : Syntax.Name) -> id.Name) ns
            let inj = genCoreStatements env ss
            [WInject (effs, inj)]
        | Syntax.EMatch (cs, o) ->
            let genO = genCoreExpr env o
            if cs.Length = 1
            then genSingleMatch env cs.[0] genO
            else failwith "Multiple match branches not yet supported."
        | Syntax.EIf (c, t, e) ->
            let cg = genCoreExpr env c
            let tg = genCoreStatements env t
            let eg = genCoreStatements env e
            List.append cg [WIf (tg, eg)]
        | Syntax.EWhile (c, b) ->
            let cg = genCoreExpr env c
            let bg = genCoreStatements env b
            [WWhile (cg, bg)]

        | Syntax.EFunctionLiteral e -> [WFunctionLiteral (genCoreExpr env e)]
        | Syntax.EListLiteral (r, es) ->
            let esg = List.collect (genCoreExpr env) es
            let consg = List.collect (fun _ -> [WPrimVar "list-cons"]) es
            if List.isEmpty r
            then List.concat [esg; [WPrimVar "list-nil"]; consg]
            else List.concat [esg; genCoreExpr env r; consg]

        | Syntax.ERecordLiteral [] -> [WEmptyRecord]
        | Syntax.ERecordLiteral exp -> genCoreExpr env exp
        | Syntax.EExtension n -> [WExtension n.Name]
        | Syntax.ERestriction n -> [WRestriction n.Name]
        | Syntax.ESelect (true, n) -> [WSelect n.Name]
        | Syntax.ESelect (false, n) -> [WPrimVar "dup"; WSelect n.Name]

        | Syntax.EVariantLiteral (n, exp) -> List.append (genCoreExpr env exp) [WVariantLiteral n.Name]
        | Syntax.EEmbedding n -> [WEmbedding n.Name]
        | Syntax.ECase ([], _) -> failwith "Improper case statement encountered during core code generation."
        | Syntax.ECase ([c], o) -> [WCase (c.Tag.Name, genCoreExpr env c.Body, genCoreExpr env o)]
        | Syntax.ECase (c :: cs, o) -> [WCase (c.Tag.Name, genCoreExpr env c.Body, genCoreWord env (Syntax.ECase (cs, o)))]

        | Syntax.EWithState ss -> genCoreStatements env ss
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
    and genCoreStatements env stmts =
        match stmts with
        | [] -> []
        | s :: ss ->
            match s with
            | Syntax.SLet clause ->
                let ce = genCoreExpr env clause.Body
                let cbs = genCoreWord env (Syntax.EMatch ([{ clause with Body = [Syntax.EStatementBlock ss] }], []))
                List.append ce cbs
            | Syntax.SLocals locals ->
                failwith "Local compilation not yet implemented."
            | Syntax.SExpression e -> List.append (genCoreExpr env e) (genCoreStatements env ss)
    and genHandler env hdlr =
        let pars = List.map (fun (p : Syntax.Name) -> p.Name) hdlr.Params
        let envWithParams = List.fold (fun e p -> Map.add p varEntry e) env pars
        let handlerEnv = Map.add "resume" { Callable = true; Empty = false } envWithParams
        {
            Name = hdlr.Name.Name.Name;
            Params = pars;
            Body = genCoreExpr handlerEnv hdlr.Body
        }
    and genSingleMatch env clause other =
        match Syntax.getFlatVars clause.Matcher with
        | Some vars ->
            let matchEnv = [for v in vars -> (v, varEntry)] |> Map.ofList |> mapUnion fst env
            [WVars (vars, genCoreExpr matchEnv clause.Body)]
        | None ->
            DotSeq.foldBack (genPatternMatch env other) (genCoreExpr env clause.Body) clause.Matcher
    and genPatternMatch env next pattern wrapped =
        match pattern with
        | Syntax.PTrue -> [WIf (wrapped, next)]
        | Syntax.PFalse -> [WPrimVar "not-bool"; WIf (wrapped, next)]
        | Syntax.PString _ -> failwith "Strings not yet supported in pattern matching"
        | Syntax.PInteger i -> [WInteger (i.Value, i.Size); WPrimVar "eq-i32"; WIf (wrapped, next)]
        | Syntax.PDecimal f -> [WDecimal (f.Value, f.Size); WPrimVar "eq-single"; WIf (wrapped, next)]
        | Syntax.PWildcard -> wrapped
        | Syntax.PRef p -> WPrimVar "get-ref" :: genPatternMatch env next p wrapped
        | Syntax.PNamed (n, p) ->
            let namedEnv = Map.add n.Name varEntry env
            [WPrimVar "dup"; WVars ([n.Name], genPatternMatch namedEnv next p wrapped)]
        | Syntax.PConstructor (id, ps) ->
            [WPrimVar "dup";
             WTestConstructorVar id.Name.Name;
             WIf (
                 WDestruct :: DotSeq.foldBack (genPatternMatch env next) wrapped ps,
                 next)]
    and genCoreExpr env expr =
        List.collect (genCoreWord env) expr


    let genCoreProgram (program : CondensedProgram) =
        let ctors = List.mapi (fun id (c: Syntax.Constructor) -> (c.Name.Name, { Id = id; Args = List.length c.Components })) program.Constructors |> Map.ofList
        let env = List.map (fun (c, b) -> (c, { Callable = true; Empty = List.isEmpty b })) program.Definitions |> Map.ofList
        let defs =
            List.filter (snd >> List.isEmpty >> not) program.Definitions |>
            List.map (fun (c, body) -> (c, genCoreExpr env body))
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
        { Main = genCoreExpr env program.Main;
          Constructors = ctors;
          Definitions = defs;
          Handlers = hdlrs;
          Effects = effs;
          BlockId = ref 0 }