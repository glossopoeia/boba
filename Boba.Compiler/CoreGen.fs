namespace Boba.Compiler

module CoreGen =

    open Boba.Core.Syntax
    open Boba.Compiler.Condenser

    type EnvEntry = {
        Callable: bool
    }

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


    let rec genCoreWord env word =
        match word with
        | Syntax.EStatementBlock ss -> genCoreStatements env ss
        | Syntax.EHandle (ps, h, hs, r) ->
            let hg = genCoreStatements env h
            let pars = List.map (fun (id : Syntax.Name) -> id.Name) ps
            let hEnv = List.fold (fun e n -> Map.add n { Callable = false } e) env pars
            let hgs = List.map (genHandler hEnv) hs
            let rg = genCoreExpr hEnv r
            [WHandle (pars, hg, hgs, rg)]
        | Syntax.EMatch (cs, o) ->
            failwith "Matching not yet implemented."
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
            let esg = List.map (genCoreExpr env) es |> List.concat
            let consg = List.map (fun _ -> [WPrimVar "list-cons"]) es |> List.concat
            if List.isEmpty r
            then List.concat [esg; [WPrimVar "list-nil"]; consg]
            else List.concat [esg; genCoreExpr env r; consg]

        | Syntax.EWithState ss -> genCoreStatements env ss
        | Syntax.ENewRef -> [WPrimVar "new-ref"]
        | Syntax.EGetRef -> [WPrimVar "get-ref"]
        | Syntax.EPutRef -> [WPrimVar "put-ref"]

        | Syntax.EUntag _ -> []

        | Syntax.EIdentifier id ->
            match id.Name.Kind with
            | Syntax.NameKind.ISmall ->
                if Map.containsKey id.Name.Name env
                then
                    if env.[id.Name.Name].Callable
                    then [WCallVar id.Name.Name]
                    else [WValueVar id.Name.Name]
                else [WPrimVar id.Name.Name]
            | Syntax.NameKind.IBig -> [WConstructorVar id.Name.Name]
            | Syntax.NameKind.IOperator -> [WOperatorVar id.Name.Name]
            | Syntax.NameKind.IPredicate -> [WTestConstructorVar id.Name.Name]

        | Syntax.EDo -> [WDo]
        | Syntax.EInteger id -> [WInteger (id.Value, id.Size)]
        | Syntax.EDecimal id -> [WDecimal (id.Value, id.Size)]
        | Syntax.EString id -> [WString id.Value]
        | Syntax.ETrue -> [WCallVar "bool-true"]
        | Syntax.EFalse -> [WCallVar "bool-false"]
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
            | Syntax.SExpression e -> genCoreExpr env e
    and genHandler env hdlr =
        let pars = List.map (fun (p : Syntax.Name) -> p.Name) hdlr.Params
        {
            Name = hdlr.Name.Name.Name;
            Params = pars;
            Body = genCoreExpr (List.fold (fun e p -> Map.add p { Callable = false } e) env pars) hdlr.Body
        }
    and genCoreExpr env expr =
        List.concat (List.map (genCoreWord env) expr)


    let genCoreProgram (program : CondensedProgram) =
        let ctors = List.mapi (fun id (c, args) -> (c, { Id = id; Args = List.length args })) program.Constructors |> Map.ofList
        let env = List.map (fun (c, _) -> (c, { Callable = true })) program.Definitions |> Map.ofList
        let defs = List.map (fun (c, body) -> (c, genCoreExpr env body)) program.Definitions |> Map.ofList
        { Main = genCoreExpr env program.Main;
          Constructors = ctors;
          Definitions = defs;
          BlockId = ref 0 }