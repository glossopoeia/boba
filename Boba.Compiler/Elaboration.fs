namespace Boba.Compiler

module Elaboration =

    open Boba.Compiler
    open Boba.Core
    open Boba.Core.Fresh
    open Boba.Core.Types
    open Boba.Core.TypeBuilder
    open Boba.Core.Environment
    open Boba.Core.Matching

    /// Generate a parameter list corresponding to the overload constraints of a function.
    /// So `Num a, Eq a => (List (List a)) (List a) --> bool` yields something like
    /// `[(Num? a, dict*2), (Eq? a, dict*1)]`, along with the elaboration of the function
    /// that takes the parameters in the proper order.
    let elaborateParams (fresh : FreshVars) ctx exp =
        // TODO: this doesn't support dotted constraints yet!
        let indCtx = DotSeq.toList ctx
        // the '*' in the name for each dictionary variable ensures uniqueness, no need to handle shadowing
        let vars = [for c in indCtx -> $"""dict*{(typeConstraintArg c |> List.head)}""".Replace(" ", "_")]
        let varPats = List.rev [for v in vars -> Syntax.PNamed (Syntax.stringToSmallName v, Syntax.PWildcard)]
        List.zip indCtx vars, [Syntax.EStatementBlock [Syntax.SLet { Matcher = DotSeq.ofList varPats; Body = [] }; Syntax.SExpression exp]]

    let smallIdentFromString s : Syntax.Identifier = { Qualifier = []; Name = Syntax.stringToSmallName s }

    let rec resolveOverload fresh env paramMap ty =
        let (TCon (constrName, _)) = typeConstraintName ty
        let over = lookupPred env constrName
        match List.filter (fun inst -> isTypeMatch fresh (qualTypeHead (fst inst).Body) ty) over.Instances with
        | [(instTy, n)] ->
            // TODO: this doesn't yet handle dotted constraints!
            let subst = typeMatchExn fresh (qualTypeHead instTy.Body) ty
            let instConstrs = qualTypeContext instTy.Body |> DotSeq.toList |> List.map (typeSubstSimplifyExn fresh subst) |> List.rev
            let elaborateInst = List.collect (resolveOverload fresh env paramMap) instConstrs
            [Syntax.EFunctionLiteral (List.append elaborateInst [Syntax.EIdentifier (smallIdentFromString n)])]
        | [] ->
            // no instance fits, which parameter fits?
            // TODO: maybe just syntactic equality on non-Boolean/non-Abelian types?
            match List.tryFind (fun (parType, _) -> ty = parType) paramMap with
            | Some (_, parVar) -> [Syntax.EIdentifier (smallIdentFromString parVar)]
            | None -> failwith $"Could not resolve overload arg {ty} with params {paramMap}"
        | _ -> failwith $"Overlapping instances detected!"

    let resolveMethod fresh env paramMap name ty =
        let over = env.Overloads.[name]
        // do we have an instance that fits?
        match List.filter (fun inst -> isTypeMatch fresh (qualTypeHead (fst inst).Body) ty) over.Instances with
        | [(instTy, n)] ->
            // TODO: this doesn't yet handle dotted constraints!
            let subst = typeMatchExn fresh (qualTypeHead instTy.Body) ty 
            let instConstrs = qualTypeContext instTy.Body |> DotSeq.toList |> List.map (typeSubstSimplifyExn fresh subst) |> List.rev
            let elaborateInst = List.collect (resolveOverload fresh env paramMap) instConstrs
            List.append elaborateInst [Syntax.EIdentifier (smallIdentFromString n)]
        | [] ->
            // no instance fits, which parameter fits?
            // TODO: maybe just syntactic equality on non-Boolean/non-Abelian types?
            match List.tryFind (fun (parType, _) -> ty = parType) paramMap with
            | Some (_, parVar) -> [Syntax.EIdentifier (smallIdentFromString parVar); Syntax.EDo]
            | None -> failwith $"Could not resolve method {name} of {ty} with params {paramMap}"
        | _ -> failwith $"Overlapping instances detected!"

    let resolveRecursive fresh env paramMap name ty =
        List.append
            [for p in paramMap -> Syntax.EIdentifier (smallIdentFromString (snd p))]
            [Syntax.EIdentifier (smallIdentFromString name)]

    let rec elaboratePlaceholders fresh env subst paramMap paramExp =
        List.map (elaborateWord fresh env subst paramMap) paramExp
    and elaborateWord fresh env subst paramMap word =
        match word with
        | Syntax.EStatementBlock stmts -> Syntax.EStatementBlock (elaborateStmts fresh env subst paramMap stmts)
        | Syntax.ENursery (n, stmts) -> Syntax.ENursery (n, elaborateStmts fresh env subst paramMap stmts)
        | Syntax.EHandle (rc, ps, hdld, hdlrs, rexpr) ->
            Syntax.EHandle
                (rc,
                 ps,
                 elaborateStmts fresh env subst paramMap hdld,
                 List.map (elaborateHandler fresh env subst paramMap) hdlrs,
                 elaboratePlaceholders fresh env subst paramMap rexpr)
        | Syntax.EInject (ns, stmts) -> Syntax.EInject (ns, List.map (elaborateStmt fresh env subst paramMap) stmts)
        | Syntax.EMatch (cs, other) -> Syntax.EMatch (List.map (elaborateMatchClause fresh env subst paramMap) cs, elaboratePlaceholders fresh env subst paramMap other)
        | Syntax.EIf (c, t, e) -> Syntax.EIf (elaboratePlaceholders fresh env subst paramMap c, elaborateStmts fresh env subst paramMap t, elaborateStmts fresh env subst paramMap e)
        | Syntax.EWhile (c, b) -> Syntax.EWhile (elaboratePlaceholders fresh env subst paramMap c, elaborateStmts fresh env subst paramMap b)
        | Syntax.EForEffect (cs, b) -> Syntax.EForEffect (List.map (elaborateAssignClause fresh env subst paramMap) cs, elaborateStmts fresh env subst paramMap b)
        | Syntax.EForComprehension (rs, cs, b) -> Syntax.EForComprehension (rs, List.map (elaborateAssignClause fresh env subst paramMap) cs, elaborateStmts fresh env subst paramMap b)
        | Syntax.EForFold (is, cs, b) ->
            Syntax.EForFold
                (List.map (elaborateFoldInits fresh env subst paramMap) is,
                 List.map (elaborateAssignClause fresh env subst paramMap) cs,
                 elaborateStmts fresh env subst paramMap b)
        | Syntax.EFunctionLiteral e -> Syntax.EFunctionLiteral (elaboratePlaceholders fresh env subst paramMap e)
        | Syntax.ETupleLiteral (r) -> Syntax.ETupleLiteral (elaboratePlaceholders fresh env subst paramMap r)
        | Syntax.EListLiteral (r) -> Syntax.EListLiteral (elaboratePlaceholders fresh env subst paramMap r)
        | Syntax.EVectorLiteral (r, es) -> Syntax.EVectorLiteral (elaboratePlaceholders fresh env subst paramMap r, List.map (elaboratePlaceholders fresh env subst paramMap) es)
        | Syntax.ERecordLiteral (r) -> Syntax.ERecordLiteral (elaboratePlaceholders fresh env subst paramMap r)
        | Syntax.EVariantLiteral (n, e) -> Syntax.EVariantLiteral (n, elaboratePlaceholders fresh env subst paramMap e)
        | Syntax.ECase (cs, o) -> Syntax.ECase (List.map (elaborateCase fresh env subst paramMap) cs, elaboratePlaceholders fresh env subst paramMap o)
        | Syntax.EWithPermission (n, thenSs, elseSs) -> Syntax.EWithPermission (n, elaborateStmts fresh env subst paramMap thenSs, elaborateStmts fresh env subst paramMap elseSs)
        | Syntax.EIfPermission (n, thenSs, elseSs) -> Syntax.EIfPermission (n, elaborateStmts fresh env subst paramMap thenSs, elaborateStmts fresh env subst paramMap elseSs)
        | Syntax.EWithState stmts -> Syntax.EWithState (elaborateStmts fresh env subst paramMap stmts)
        | Syntax.EMethodPlaceholder (name, ty) ->
            Syntax.EStatementBlock [Syntax.SExpression (resolveMethod fresh env paramMap name (typeSubstSimplifyExn fresh subst ty))]
        | Syntax.ERecursivePlaceholder (name, ty) ->
            Syntax.EStatementBlock [Syntax.SExpression (resolveRecursive fresh env paramMap name (typeSubstSimplifyExn fresh subst ty))]
        | Syntax.EOverloadPlaceholder ty ->
            Syntax.EStatementBlock [Syntax.SExpression (resolveOverload fresh env paramMap (typeSubstSimplifyExn fresh subst ty))]
        | _ -> word
    and elaborateStmts fresh env subst paramMap stmts = List.map (elaborateStmt fresh env subst paramMap) stmts
    and elaborateStmt fresh env subst paramMap stmt =
        match stmt with
        | Syntax.SLet matcher -> Syntax.SLet (elaborateMatchClause fresh env subst paramMap matcher)
        | Syntax.SLocals _ -> failwith $"Elaboration for local functions not yet implemented."
        | Syntax.SExpression exp -> Syntax.SExpression (elaboratePlaceholders fresh env subst paramMap exp)
    and elaborateMatchClause fresh env subst paramMap clause =
        { clause with Body = elaboratePlaceholders fresh env subst paramMap clause.Body }
    and elaborateHandler fresh env subst paramMap handler =
        { handler with Body = elaboratePlaceholders fresh env subst paramMap handler.Body }
    and elaborateAssignClause fresh env subst paramMap assign =
        { assign with Assigned = elaboratePlaceholders fresh env subst paramMap assign.Assigned }
    and elaborateFoldInits fresh env subst paramMap init =
        { init with Assigned = elaboratePlaceholders fresh env subst paramMap init.Assigned }
    and elaborateCase fresh env subst paramMap case =
        { case with Body = elaboratePlaceholders fresh env subst paramMap case.Body }

    let elaborateOverload fresh env subst ctx exp =
        let paramMap, paramExp = elaborateParams fresh ctx exp
        elaboratePlaceholders fresh env subst paramMap paramExp