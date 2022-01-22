namespace Boba.Compiler

module Inference =

    open System
    open Boba.Core
    open Boba.Core.Common
    open Boba.Core.Kinds
    open Boba.Core.Types
    open Boba.Core.TypeBuilder
    open Boba.Core.Unification
    open Boba.Core.Fresh
    open Boba.Core.Environment
    open Boba.Core.Predicates
    open Renamer

    let map3 f ls =
        let mapped = List.map f ls
        (List.map (fun (x, _, _) -> x) mapped, List.map (fun (_, x, _) -> x) mapped, List.map (fun (_, _, x) -> x) mapped)

    /// The key inference rule in Boba. Composed words infer their types separately,
    /// then unify the function attributes. The data components unify in a particular
    /// way: the output of the left word unifies with the input of the right word.
    /// This means that the resulting expression has an input of the left word and
    /// and output of the right word, as we would expect from composition.
    /// 
    /// Some of the function attributes are unified, but the Boolean ones are accumulated.
    /// Totality and validity (unsafe code) are accumulated via conjunction, while uniqueness
    /// (which is always false at the expression level) is accumulated via disjunction.
    let composeWordTypes leftType rightType =
        let (le, lp, lt, li, lo) = functionValueTypeComponents leftType.Head
        let (re, rp, rt, ri, ro) = functionValueTypeComponents rightType.Head
        let resTy =
            qualType (List.append leftType.Context rightType.Context)
                (mkFunctionValueType le lp (typeAnd lt rt) li ro
                    (typeAnd (valueTypeValidity leftType.Head) (valueTypeValidity rightType.Head))
                    (typeOr (valueTypeSharing leftType.Head) (valueTypeSharing rightType.Head)))
        let effConstr = { Left = le; Right = re }
        let permConstr = { Left = lp; Right = rp }
        let insOutsConstr = { Left = lo; Right = ri }
        (resTy, [effConstr; permConstr; insOutsConstr])

    /// Generates a simple polymorphic expression type of the form `(a... -> a...)`
    let freshIdentity (fresh : FreshVars) =
        let io = TSeq (freshSequenceVar fresh)
        let e = freshEffectVar fresh
        let p = freshPermVar fresh
        qualType [] (mkFunctionValueType e p totalAttr io io validAttr sharedAttr)

    /// Generates a simple polymorphic expression type of the form `(a... -> b...)`
    /// Useful for recursive function templates.
    let freshTransform (fresh : FreshVars) =
        let i = TSeq (freshSequenceVar fresh)
        let o = TSeq (freshSequenceVar fresh)
        let (e, p, t) = freshFunctionAttributes fresh
        qualType [] (mkFunctionValueType e p t i o validAttr sharedAttr)

    /// Generates a simple polymorphic expression type of the form `(a... -> a... ty)`
    let freshPush (fresh : FreshVars) total ty =
        assert (typeKindExn ty = KValue)
        let rest = freshSequenceVar fresh
        let i = TSeq rest
        let o = TSeq (DotSeq.SInd (ty, rest))
        let e = freshEffectVar fresh
        let p = freshPermVar fresh
        qualType [] (mkFunctionValueType e p total i o validAttr sharedAttr)

    let freshPushWord (fresh : FreshVars) ty word = (freshPush fresh totalAttr ty, [], [word])
    
    let freshPopped (fresh: FreshVars) tys =
        let rest = freshSequenceVar fresh
        let o = TSeq rest
        let i = TSeq (DotSeq.append (DotSeq.ofList (List.rev tys)) rest)
        let e = freshEffectVar fresh
        let p = freshPermVar fresh
        qualType [] (mkFunctionValueType e p totalAttr i o validAttr sharedAttr)

    let freshNonSeqPoppedPush (fresh: FreshVars) tys res =
        let rest = DotSeq.SEnd
        let o = TSeq (DotSeq.ind res rest)
        let i = TSeq (DotSeq.append (DotSeq.ofList (List.rev tys)) rest)
        let e = freshEffectVar fresh
        let p = freshPermVar fresh
        qualType [] (mkFunctionValueType e p totalAttr i o validAttr sharedAttr)
    
    /// Generate a qualified type of the form `(a... ty1 ty2 ... --> b...)`.
    let freshResume (fresh: FreshVars) tys outs =
        let i = TSeq (DotSeq.append (DotSeq.ofList (List.rev tys)) (freshSequenceVar fresh))
        let (e, p, t) = freshFunctionAttributes fresh
        qualType [] (mkFunctionValueType e p t i outs validAttr sharedAttr)
    
    /// Generate a type scheme of the form `(a... -> a... ty)` in which all variables are quantified
    /// except those in `ty`.
    let freshPushScheme fresh total ty =
        let body = freshPush fresh total ty
        let quant = Set.difference (qualFreeWithKinds body) (typeFreeWithKinds ty) |> Set.toList
        { Quantified = quant; Body = body }

    /// Generate a type scheme of the form `(a... -> a... v)` in which the only unquantified variables
    /// are those in `v`.
    let freshVarScheme fresh = freshPushScheme fresh totalAttr (freshValueComponentType fresh)

    /// The sharing attribute on a closure is the disjunction of all of the free variables referenced
    /// by the closure, forcing it to be unique if any of the free variables it references are also unique.
    let sharedClosure env expr =
        List.ofSeq (Boba.Compiler.Syntax.exprFree expr)
        |> List.map (lookup env >> Option.map (fun entry -> schemeSharing entry.Type))
        |> List.collect Option.toList
        |> attrsToDisjunction KSharing

    let getWordEntry env name =
        match lookup env name with
        | Some entry -> entry
        | None -> failwith $"Could not find {name} in the environment"

    /// Here, when we instantiate a type from the type environment, we also do inline dictionary
    /// passing, putting in placeholders for the dictionaries that will get resolved to either a
    /// dictionary parameter or dictionary value during generalization.
    /// More details on this implementation tactic: "Implementing Type Classes",
    /// https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.53.3952&rep=rep1&type=pdf
    let instantiateAndAddPlaceholders fresh env name word =
        let entry = getWordEntry env name
        let instantiated = instantiateExn fresh entry.Type
        let replaced = 
            if entry.IsClassMethod
            then 
                [Syntax.EMethodPlaceholder (name, instantiated.Context.Head)]
            elif entry.IsRecursive
            then [Syntax.ERecursivePlaceholder { Name = name; Argument = instantiated.Head }]
            else List.append (List.map Syntax.EOverloadPlaceholder instantiated.Context) [word]
        (instantiated, [], replaced)

    /// Given two function types which represent two 'branches' of an expression
    /// e.g. in an if-then-else, generates constraints for only the parts that
    /// should be unified, and returns a type composing the parts that should be
    /// composed (i.e. totality, validity, sharing)
    let unifyBranches br1 br2 =
        let (br1e, br1p, br1t, br1i, br1o) = functionValueTypeComponents br1.Head
        let (br2e, br2p, br2t, br2i, br2o) = functionValueTypeComponents br2.Head
        let effConstr = { Left = br1e; Right = br2e }
        let permConstr = { Left = br1p; Right = br2p }
        let insConstr = { Left = br1i; Right = br2i }
        let outsConstr = { Left = br1o; Right = br2o }
        let totalComp = typeAnd br1t br2t
        let validComp = typeAnd (valueTypeValidity br1.Head) (valueTypeValidity br2.Head)
        let shareComp = typeOr (valueTypeSharing br1.Head) (valueTypeSharing br2.Head)
        let unifiedType = qualType (List.append br1.Context br2.Context) (mkFunctionValueType br1e br1p totalComp br1i br1o validComp shareComp)
        unifiedType, [effConstr; permConstr; insConstr; outsConstr]

    let rec inferPattern fresh env pattern =
        match pattern with
        | Syntax.PTuple _ -> failwith "Inference for tuple patterns not yet implemented."
        | Syntax.PList _ -> failwith "Inference for list patterns not yet implemented."
        | Syntax.PVector _ -> failwith "Inference for vector patterns not yet implemented."
        | Syntax.PSlice _ -> failwith "Inference for slice patterns not yet implemented."
        | Syntax.PRecord _ -> failwith "Inference for record patterns not yet implemented."
        | Syntax.PConstructor (name, ps) ->
            failwith "Inference for algebraic data constructors not yet implemented."
            let vs, cs, infPs = DotSeq.map (inferPattern fresh env) ps |> DotSeq.toList |> List.unzip3
            let res = freshValueComponentType fresh
            let templateTy = instantiateExn fresh (getWordEntry env name.Name.Name).Type
            let dataTy = freshNonSeqPoppedPush fresh infPs res
            List.concat vs, { Left = templateTy.Head; Right = dataTy.Head } :: List.concat cs, res
        | Syntax.PNamed (n, p) ->
            let (vs, cs, ty) = inferPattern fresh env p
            (Syntax.nameToString n, ty) :: vs, cs, ty
        | Syntax.PRef r ->
            let vs, cs, ty = inferPattern fresh env r
            let expanded = freshValueComponentType fresh
            let heap = freshHeapVar fresh
            let ref =
                mkRefValueType heap expanded
                    (typeAnd (freshValidityVar fresh) (valueTypeValidity expanded))
                    (typeOr (freshShareVar fresh) (valueTypeSharing expanded))
            vs, { Left = ty; Right = expanded } :: cs, ref
        | Syntax.PWildcard -> ([], [], freshValueVar fresh)
        | Syntax.PInteger i -> ([], [], freshIntValueType fresh i.Size (freshValidityVar fresh))
        | Syntax.PDecimal d -> ([], [], freshFloatValueType fresh d.Size (freshValidityVar fresh))
        | Syntax.PString _ -> ([], [], freshStringValueType fresh (freshValidityVar fresh))
        | Syntax.PTrue _ -> ([], [], freshBoolValueType fresh (freshValidityVar fresh))
        | Syntax.PFalse _ -> ([], [], freshBoolValueType fresh (freshValidityVar fresh))
    
    let extendPushVars fresh env varTypes =
        List.fold (fun env vt -> extendVar env (fst vt) (freshPushScheme fresh totalAttr (snd vt))) env varTypes

    let rec inferExpr (fresh : FreshVars) env expr =
        let exprInferred = List.map (inferWord fresh env) expr
        let composed =
            List.fold
                (fun (ty, constrs, expanded) (next, newConstrs, nextExpand) ->
                    let (uniTy, uniConstrs) = composeWordTypes ty next
                    (uniTy, append3 constrs newConstrs uniConstrs, List.append expanded nextExpand))
                (freshIdentity fresh, [], [])
                exprInferred
        composed
    and inferWord fresh env word =
        match word with
        | Syntax.EStatementBlock ss ->
            let (ssTy, ssCnstrs, ssPlc) = inferBlock fresh env ss
            (ssTy, ssCnstrs, [Syntax.EStatementBlock ssPlc])
        | Syntax.EHandle (ps, hdld, hdlrs, aft) ->
            inferHandle fresh env ps hdld hdlrs aft
        | Syntax.EInject _ -> failwith $"Inference not yet implemented for inject expressions."
        | Syntax.EMatch (cs, o) -> inferMatch fresh env cs o
        | Syntax.EIf (cond, thenClause, elseClause) ->
            // infer types for the sub expressions separately
            let (infCond, constrsCond, condExpand) = inferExpr fresh env cond
            let (infThen, constrsThen, thenExpand) = inferBlock fresh env thenClause
            let (infElse, constrsElse, elseExpand) = inferBlock fresh env elseClause
            let condTemplate = freshPopped fresh [freshBoolValueType fresh validAttr]
            // make sure the 'then' and 'else' branches unify to the same type
            let infThenElse, thenElseConstrs = unifyBranches infThen infElse
            let (condJoin, constrsCondJoin) = composeWordTypes infCond condTemplate
            let (infJoin, constrsJoin) = composeWordTypes condJoin infThenElse

            let constrs = List.concat [constrsCond; constrsThen; constrsElse; constrsJoin; constrsCondJoin; thenElseConstrs]
            infJoin, constrs, [Syntax.EIf (condExpand, thenExpand, elseExpand)]
        | Syntax.EWhile (cond, body) ->
            let (infCond, constrsCond, condExpand) = inferExpr fresh env cond
            let (infBody, constrsBody, bodyExpand) = inferBlock fresh env body
            let condTemplate = freshPopped fresh [freshBoolValueType fresh validAttr]
            let condJoin, constrsCondJoin = composeWordTypes infCond condTemplate
            let bodyJoin, constrsBodyJoin = composeWordTypes condJoin infBody
            let whileJoin, constrsWhileJoin = composeWordTypes bodyJoin condJoin
            let constrs = List.concat [constrsCond; constrsBody; constrsCondJoin; constrsBodyJoin; constrsWhileJoin]
            whileJoin, constrs, [Syntax.EWhile (condExpand, bodyExpand)]
        | Syntax.ERecordLiteral [] ->
            // record literals with no splat expression just create an empty record
            let ne = freshEffectVar fresh
            let np = freshPermVar fresh
            let rest = freshSequenceVar fresh
            let i = TSeq rest
            let o = TSeq (DotSeq.ind (mkRecordValueType (TEmptyRow KField) (freshValidityVar fresh) (freshShareVar fresh)) rest)
            (qualType [] (mkFunctionValueType ne np totalAttr i o validAttr sharedAttr), [], [Syntax.ERecordLiteral []])
        | Syntax.ERecordLiteral exp ->
            // the splat expression in a record literal must put a record on top of the stack
            let (infExp, constrsExp, expExpand) = inferExpr fresh env exp
            let ne = freshEffectVar fresh
            let np = freshPermVar fresh
            let nr = freshFieldVar fresh
            let recVal = mkRecordValueType nr (freshValidityVar fresh) (freshShareVar fresh)
            let rest = freshSequenceVar fresh
            let io = TSeq (DotSeq.ind recVal rest)
            let verifyRecTop = qualType [] (mkFunctionValueType ne np totalAttr io io validAttr sharedAttr)
            let (infVer, constrsVer) = composeWordTypes infExp verifyRecTop
            infVer, List.append constrsExp constrsVer, [Syntax.ERecordLiteral expExpand]
        | Syntax.EExtension name ->
            let ne = freshEffectVar fresh
            let np = freshPermVar fresh
            let fieldVal = mkValueType (freshDataVar fresh) (freshValidityVar fresh) (freshShareVar fresh)
            let nr = freshFieldVar fresh
            let recRow = mkFieldRowExtend name.Name fieldVal nr
            let nv = freshValidityVar fresh
            let ns = freshShareVar fresh
            let recVal = mkRecordValueType recRow nv ns
            let rest = freshSequenceVar fresh
            let i = TSeq (DotSeq.ind fieldVal (DotSeq.ind (mkRecordValueType nr nv ns) rest))
            let o = TSeq (DotSeq.ind recVal rest)
            (qualType [] (mkFunctionValueType ne np totalAttr i o validAttr sharedAttr), [], [Syntax.EExtension name])
        | Syntax.ERestriction name ->
            let ne = freshEffectVar fresh
            let np = freshPermVar fresh
            let fieldVal = freshValueVar fresh
            let nr = freshFieldVar fresh
            let nv = freshValidityVar fresh
            let ns = freshShareVar fresh
            let rest = freshSequenceVar fresh
            let i = TSeq (DotSeq.ind (mkRecordValueType (mkFieldRowExtend name.Name fieldVal nr) nv ns) rest)
            let o = TSeq (DotSeq.ind (mkRecordValueType nr nv ns) rest)
            (qualType [] (mkFunctionValueType ne np totalAttr i o validAttr sharedAttr), [], [Syntax.ERestriction name])
        | Syntax.ESelect (false, name) ->
            // false = don't leave the record on the stack, just pop it. Makes selecting shared data
            // out of a unique record multiple times difficult, but probably easiest to use otherwise.
            let ne = freshEffectVar fresh
            let np = freshPermVar fresh
            let rs = freshShareVar fresh
            let fieldVal = mkValueType (freshDataVar fresh) (freshValidityVar fresh) rs
            let nr = freshFieldVar fresh
            let nv = freshValidityVar fresh
            let ns = freshShareVar fresh
            let rest = freshSequenceVar fresh
            let i = TSeq (DotSeq.ind (mkRecordValueType (mkFieldRowExtend name.Name fieldVal nr) nv (typeOr rs ns)) rest)
            let o = TSeq (DotSeq.ind fieldVal rest)
            (qualType [] (mkFunctionValueType ne np totalAttr i o validAttr sharedAttr), [], [Syntax.ESelect (false, name)])
        | Syntax.ESelect (true, name) ->
            // true = leave the record on the stack while selecting shared data out of it. Makes it easier
            // to select shared data out of a unique record multiple times, but otherwise not useful.
            let ne = freshEffectVar fresh
            let np = freshPermVar fresh
            let fieldVal = mkValueType (freshDataVar fresh) (freshValidityVar fresh) sharedAttr
            let nr = freshFieldVar fresh
            let nv = freshValidityVar fresh
            let recVal = mkRecordValueType (mkFieldRowExtend name.Name fieldVal nr) nv (freshShareVar fresh)
            let rest = freshSequenceVar fresh
            let i = TSeq (DotSeq.ind recVal rest)
            let o = TSeq (DotSeq.ind fieldVal (DotSeq.ind recVal rest))
            (qualType [] (mkFunctionValueType ne np totalAttr i o validAttr sharedAttr), [], [Syntax.ESelect (true, name)])
        | Syntax.EVariantLiteral (name, exp) ->
            let (infExp, constrsExp, expExpand) = inferExpr fresh env exp
            let ne = freshEffectVar fresh
            let np = freshPermVar fresh
            let fieldVal = freshValueVar fresh
            let nr = freshFieldVar fresh
            let rest = freshSequenceVar fresh
            let i = TSeq (DotSeq.ind fieldVal rest)
            let o = TSeq (DotSeq.ind (mkVariantValueType (mkFieldRowExtend name.Name fieldVal nr) (freshValidityVar fresh) (freshShareVar fresh)) rest)
            let varLit = qualType [] (mkFunctionValueType ne np totalAttr i o validAttr sharedAttr)
            let varInf, varConstrs = composeWordTypes infExp varLit
            varInf, List.append constrsExp varConstrs, [Syntax.EVariantLiteral (name, expExpand)]
        | Syntax.EEmbedding name ->
            let ne = freshEffectVar fresh
            let np = freshPermVar fresh
            let fieldVal = freshValueVar fresh
            let nr = freshFieldVar fresh
            let rest = freshSequenceVar fresh
            let nv = freshValidityVar fresh
            let ns = freshShareVar fresh
            let i = TSeq (DotSeq.ind (mkVariantValueType nr nv ns) rest)
            let o = TSeq (DotSeq.ind (mkVariantValueType (mkFieldRowExtend name.Name fieldVal nr) nv ns) rest)
            (qualType [] (mkFunctionValueType ne np totalAttr i o validAttr sharedAttr), [], [Syntax.EEmbedding name])
        | Syntax.ECase (cs, other) ->
            let cShare = freshShareVar fresh
            let cValid = freshValidityVar fresh
            let (infCs, constrsCs, csExpand) = List.map (inferCaseClause fresh env cValid cShare) cs |> List.unzip3
            let (infOther, constrsOther, otherExp) = inferExpr fresh env other
            let clauseJoins = List.pairwise (infOther :: infCs) |> List.map (fun (l, r) -> { Left = l.Head; Right = r.Head })
            infOther, List.concat [List.concat constrsCs; clauseJoins; constrsOther], [Syntax.ECase (csExpand, otherExp)]
        | Syntax.EWithState e ->
            failwith "Type inference for with-state not yet implemented."
        | Syntax.ENewRef ->
            // newref : a... b^u --st[h]-> a... ref<h,b^u>^v
            let rest = freshSequenceVar fresh
            let e = freshEffectVar fresh
            let p = freshPermVar fresh
            let heap = freshHeapVar fresh
            let value = freshValueComponentType fresh
            let ref = mkRefValueType heap value (freshValidityVar fresh) (freshShareVar fresh)
            let st = typeApp (TPrim PrState) heap
            let i = TSeq (DotSeq.ind value rest)
            let o = TSeq (DotSeq.ind ref rest)
            let expr = mkFunctionValueType (mkRowExtend st e) p totalAttr i o validAttr sharedAttr
            (qualType [] expr, [], [Syntax.ENewRef])
        | Syntax.EGetRef ->
            failwith "Type inference for get@ not yet implemented."
        | Syntax.EPutRef ->
            failwith "Type inference for put@ not yet implemented."
        | Syntax.EFunctionLiteral exp ->
            let (eTy, eCnstrs, ePlc) = inferExpr fresh env exp
            let ne = freshEffectVar fresh
            let np = freshPermVar fresh
            let asValue = mkValueType (valueTypeData eTy.Head) (valueTypeValidity eTy.Head) (sharedClosure env exp)
            let rest = freshSequenceVar fresh
            let i = TSeq rest
            let o = TSeq (DotSeq.ind asValue rest)
            (qualType eTy.Context (mkFunctionValueType ne np totalAttr i o validAttr sharedAttr), eCnstrs, [Syntax.EFunctionLiteral ePlc])
        | Syntax.EDo ->
            let irest = freshSequenceVar fresh
            let i = TSeq irest
            let o = TSeq (freshSequenceVar fresh)
            let s = freshShareVar fresh
            let (e, p, t) = freshFunctionAttributes fresh
            let v = freshValidityVar fresh
            let called = mkFunctionValueType e p t i o v s
            let caller = mkFunctionValueType e p t (TSeq (DotSeq.ind called irest)) o v sharedAttr
            (qualType [] caller, [], [Syntax.EDo])
        | Syntax.EIdentifier id ->
            instantiateAndAddPlaceholders fresh env id.Name.Name word
        | Syntax.EDecimal d ->
            freshPushWord fresh (freshFloatValueType fresh d.Size validAttr) word
        | Syntax.EInteger i ->
            freshPushWord fresh (freshIntValueType fresh i.Size validAttr) word
        | Syntax.EString _ ->
            freshPushWord fresh (freshStringValueType fresh validAttr) word
        | Syntax.ETrue ->
            freshPushWord fresh (freshBoolValueType fresh validAttr) word
        | Syntax.EFalse ->
            freshPushWord fresh (freshBoolValueType fresh validAttr) word

    /// Match expressions have an optional `otherwise` expression that behaves as a catch-all.
    /// If this expression is not present, we must evaluate the pattern matches to determine whether
    /// we should inject a 'may fail pattern match' exception into the effect row type. If the expression
    /// is present, we definitely don't have to, because if all matches fail the `otherwise` expression
    /// will be evaluated on the inputs. Since we unify all branches of a match expression together, all
    /// branches will take the same input types and return the same output types. Totality of the expression
    /// is thus the conjunction of all its branches (if one is not total, the whole thing is not total),
    /// and if one of the branches calls unsafe code, the whole expression must be deemed unsafe.
    /// Most components of the expression type can be directly unified, but the Boolean attributes must
    /// be accumulated rather than unified, so we use the special `unifyBranches` function.
    and inferMatch fresh env clauses other =
        let unifyBranchFold (ty, constrs) next =
            let ret, moreConstrs = unifyBranches ty next
            ret, List.append moreConstrs constrs
        match other with
        | [] ->
            let (infCs, constrsCs, csExpand) = List.map (inferMatchClause fresh env) clauses |> List.unzip3
            let joinType, joinConstrs = List.fold unifyBranchFold (infCs.Head, []) infCs.Tail
            // TODO: update the inferred type here with possible match failure effect, since the else clause is elided
            joinType, List.concat [List.concat constrsCs; joinConstrs], [Syntax.EMatch (csExpand, [])]
        | otherExpr ->
            let (infOther, constrsOther, otherExpand) = inferExpr fresh env otherExpr
            let (infCs, constrsCs, csExpand) = List.map (inferMatchClause fresh env) clauses |> List.unzip3
            let joinType, joinConstrs = List.fold unifyBranchFold (infOther, []) infCs
            joinType, List.concat [constrsOther; List.concat constrsCs; joinConstrs], [Syntax.EMatch (csExpand, otherExpand)]
    and inferBlock fresh env stmts =
        match stmts with
        | [] -> (freshIdentity fresh, [], [])
        | Syntax.SLet { Matcher = ps; Body = b } :: ss ->
            let (bTy, bCnstr, bPlc) = inferExpr fresh env b
            let varTypes, constrsP, poppedTypes = map3 (inferPattern fresh env) (DotSeq.toList ps)
            let varTypes = List.concat varTypes
            let varEnv = extendPushVars fresh env varTypes
            let (ssTy, ssCnstr, ssPlc) = inferBlock fresh varEnv ss
            let popped = freshPopped fresh poppedTypes

            let (uniTyL, uniConstrL) = composeWordTypes bTy popped
            let (uniTyR, uniConstrR) = composeWordTypes uniTyL ssTy
            (uniTyR, List.concat [bCnstr; List.concat constrsP; ssCnstr; uniConstrL; uniConstrR],
                Syntax.SLet { Matcher = ps; Body = bPlc } :: ssPlc)
        | Syntax.SLocals _ :: ss -> failwith "Local functions not yet implemented."
        | Syntax.SExpression e :: ss ->
            let (eTy, eCnstr, ePlc) = inferExpr fresh env e
            let (sTy, sCnstr, sPlc) = inferBlock fresh env ss
            let (uniTy, uniConstrs) = composeWordTypes eTy sTy
            (uniTy, append3 eCnstr sCnstr uniConstrs, Syntax.SExpression ePlc :: sPlc)
    and inferHandle fresh env hdlParams body handlers after =
        assert (handlers.Length > 0)
        let (hdldTy, hdldCnstrs, hdldPlc) = inferBlock fresh env body
        let hdlrTypeTemplates = List.map (fun (h: Boba.Compiler.Syntax.Handler) -> (getWordEntry env h.Name.Name.Name).Type) handlers

        // get the basic effect row type of the effect
        let exHdlrType = instantiateExn fresh hdlrTypeTemplates.[0]
        let effRow = functionValueTypeEffect exHdlrType.Head
        let effCnstr = { Left = effRow; Right = functionValueTypeEffect hdldTy.Head }
        let effHdldTy = 
            {
                Context = hdldTy.Context;
                Head = updateFunctionValueTypeEffect hdldTy.Head (rowTypeTail effRow)
            }

        let psTypes = List.map (fun (p : Syntax.Name) -> (p.Name, freshValueComponentType fresh)) hdlParams
        let psEnv = extendPushVars fresh env psTypes

        let (aftTy, aftCnstrs, aftPlc) = inferExpr fresh psEnv after
        let hdlResult = functionValueTypeOuts aftTy.Head
        let (hdlrTys, hdlrCnstrs, hdlrPlcs) = map3 (inferHandler fresh psEnv psTypes hdlResult) handlers

        let argPopped = freshPopped fresh (List.map snd psTypes)
        let hdlType, hdlCnstrs = composeWordTypes argPopped effHdldTy
        let finalTy, finalCnstrs = composeWordTypes hdlType aftTy
        let replaced = Syntax.EHandle (hdlParams, hdldPlc, hdlrPlcs, aftPlc)
        finalTy, List.concat [finalCnstrs; hdlCnstrs; List.concat hdlrCnstrs; aftCnstrs; [effCnstr]; hdldCnstrs], [replaced]
    and inferHandler fresh env hdlParams resultTy hdlr =
        // TODO: account for fixed parameters here too
        // TODO: this doesn't account for overloaded dictionary parameters yet
        let psTypes = List.map (fun (p: Syntax.Name) -> (p.Name, freshValueComponentType fresh)) hdlr.Params
        let psEnv = extendPushVars fresh env psTypes
        let resumeTy = freshResume fresh (List.map snd hdlParams) resultTy
        let resEnv = extendVar psEnv "resume" { Quantified = []; Body = resumeTy }

        let (bInf, bCnstrs, bPlc) = inferExpr fresh resEnv hdlr.Body
        let argPopped = freshPopped fresh (List.map snd psTypes)
        let (hdlrTy, hdlrCnstrs) = composeWordTypes argPopped bInf

        let hdlrTemplate = freshResume fresh (List.map snd psTypes) resultTy
        hdlrTy, { Left = hdlrTemplate.Head; Right = hdlrTy.Head } :: List.append hdlrCnstrs bCnstrs, { hdlr with Body = bPlc }
    and inferMatchClause fresh env clause =
        let varTypes, constrsP, poppedTypes =
            DotSeq.map (inferPattern fresh env) clause.Matcher
            |> DotSeq.toList
            |> List.unzip3
        let varTypes = List.concat varTypes
        let varEnv = extendPushVars fresh env varTypes
        let bTy, bCnstr, bPlc = inferExpr fresh varEnv clause.Body
        let popped = freshPopped fresh poppedTypes

        let uniTy, uniConstr = composeWordTypes popped bTy
        uniTy, List.concat [bCnstr; List.concat constrsP; uniConstr], { Matcher = clause.Matcher; Body = bPlc }
    and inferCaseClause fresh env caseValid caseShare clause =
        let infBody, constrsBody, bodyExp = inferExpr fresh env clause.Body
        let ne = freshEffectVar fresh
        let np = freshPermVar fresh
        let fs = freshShareVar fresh
        let fv = freshValidityVar fresh
        let fieldVal = mkValueType (freshDataVar fresh) fv fs
        let nr = freshFieldVar fresh
        let rest = freshSequenceVar fresh
        let i = TSeq (DotSeq.ind (mkVariantValueType (mkFieldRowExtend clause.Tag.Name fieldVal nr) (typeAnd fv caseValid) (typeOr fs caseShare)) rest)
        let o = TSeq (DotSeq.ind fieldVal rest)
        let destruct = qualType [] (mkFunctionValueType ne np totalAttr i o validAttr sharedAttr)
        let infDest, constrsDest = composeWordTypes destruct infBody
        infDest, List.append constrsBody constrsDest, { clause with Body = bodyExp }

    let lookupTypeOrFail env name ctor =
        match lookupType env name with
        | Some k -> k, [], ctor name k
        | None -> failwith $"Could not find '{name}' in type environment during kind inference."

    let freshKind (fresh : FreshVars) = KVar (fresh.Fresh "k")

    let freshCtor fresh ctor =
        let k = freshKind fresh
        k, [], ctor k

    let rec kindInfer fresh env sty =
        match sty with
        | Syntax.STVar n -> lookupTypeOrFail env n.Name typeVar
        | Syntax.STDotVar n -> lookupTypeOrFail env n.Name typeDotVar
        | Syntax.STCon n -> lookupTypeOrFail env n.Name.Name typeCon
        | Syntax.STPrim p -> primKind p, [], TPrim p
        | Syntax.STTrue -> freshCtor fresh TTrue
        | Syntax.STFalse -> freshCtor fresh TFalse
        | Syntax.STAnd (l, r) -> simpleBinaryCon fresh env l r TAnd
        | Syntax.STOr (l, r) -> simpleBinaryCon fresh env l r TOr
        | Syntax.STNot n -> simpleUnaryCon fresh env n TNot
        | Syntax.STAbelianOne -> freshCtor fresh TAbelianOne
        | Syntax.STExponent (b, p) -> simpleUnaryCon fresh env b (fun t -> TExponent (t, Int32.Parse p.Value))
        | Syntax.STMultiply (l, r) -> simpleBinaryCon fresh env l r TMultiply
        | Syntax.STFixedConst c -> KFixed, [], TFixedConst (Int32.Parse c.Value)
        | Syntax.STRowExtend ->
            let k = freshKind fresh
            karrow k (karrow (KRow k) (KRow k)), [], TRowExtend k
        | Syntax.STRowEmpty ->
            let k = freshKind fresh
            KRow k, [], TEmptyRow k
        | Syntax.STSeq ts ->
            if DotSeq.length ts = 0
            then
                let seqKind = freshKind fresh
                KSeq seqKind, [{ LeftKind = seqKind; RightKind = KValue }], TSeq DotSeq.SEnd
            else
                let ks = DotSeq.map (kindInfer fresh env) ts
                let seqKind =
                    DotSeq.at 0 ks
                    |> Option.defaultWith (fun () -> failwith "No element in type sequence")
                    |> (fun (k, _, _) -> k)
                let cstrs = DotSeq.map (fun (_, cs, _) -> cs) ks |> DotSeq.fold List.append []
                let allSeqKindsEq = DotSeq.map (fun (k, _, _) -> { LeftKind = seqKind; RightKind = k }) ks |> DotSeq.toList
                // Special constraint for sequences, which must have Value element kind
                let allCstrs = append3 [{ LeftKind = seqKind; RightKind = KValue }] allSeqKindsEq cstrs
                KSeq seqKind, allCstrs, TSeq (DotSeq.map (fun (_, _, t) -> t) ks)
        | Syntax.STApp (l, r) ->
            let (lk, lcstrs, lt) = kindInfer fresh env l
            let (rk, rcstrs, rt) = kindInfer fresh env r
            let ret = freshKind fresh
            ret, append3 [{ LeftKind = lk; RightKind = karrow rk ret }] lcstrs rcstrs, TApp (lt, rt)
    and simpleBinaryCon fresh env l r ctor =
        let (lk, lcstrs, lt) = kindInfer fresh env l
        let (rk, rcstrs, rt) = kindInfer fresh env r
        lk, append3 [{ LeftKind = lk; RightKind = rk }] lcstrs rcstrs, ctor (lt, rt)
    and simpleUnaryCon fresh env b ctor =
        let (k, cstrs, t) = kindInfer fresh env b
        k, cstrs, ctor t

    let kindAnnotateQual fresh env (qual : Syntax.SQualifiedType) =
        let kenv = Syntax.stypeFree qual.SHead |> Set.fold (fun e v -> addTypeCtor e v (freshKind fresh)) env
        try
            let (inf, constraints, ty) = kindInfer fresh kenv qual.SHead
            // TODO: annotate and convert the predicate context here too
            let subst = solveKindConstraints constraints
            { Context = []; Head = typeKindSubstExn subst ty }
        with
            | KindUnifyMismatchException (l, r) -> failwith $"{l}:{r} failed to unify."
            
    
    let testAmbiguous reduced normalized =
        if isAmbiguousPredicates reduced (typeFree normalized.Head)
        then failwith "Ambiguous predicates"//(AmbiguousPredicates reduced)
        else qualType reduced normalized.Head

    let inferTop fresh env expr =
        try
            let (inferred, constrs, expanded) = inferExpr fresh env expr
            let subst = solveAll fresh constrs
            let normalized = qualSubstExn subst inferred
            let reduced = contextReduceExn fresh normalized.Context env
            (testAmbiguous reduced normalized, expanded)
        with
            | UnifyKindMismatch (t1, t2, k1, k2) -> failwith $"{t1}:{k1} kind mismatch with {t2}:{k2}"
            | UnifyRigidRigidMismatch (l, r) -> failwith $"{l} cannot unify with {r}"
    

    let inferFunction fresh env (fn: Syntax.Function) =
        // TODO: add fixed params to env
        let (ty, exp) = inferTop fresh env fn.Body
        let genTy = schemeFromQual (simplifyQual ty)
        (genTy, { fn with Body = exp })

    let inferRecFuncs fresh env (fns: List<Syntax.Function>) =
        // TODO: add fixed params to env
        let emptyScheme q = { Quantified = []; Body = q }
        let recEnv = List.fold (fun tenv (fn : Syntax.Function) -> extendRec tenv fn.Name.Name (freshTransform fresh |> emptyScheme)) env fns
        let tys, constrs, exps = map3 (fun (fn : Syntax.Function) -> inferExpr fresh recEnv fn.Body) fns
        let subst = solveAll fresh (List.concat constrs)
        let norms = List.map (qualSubstExn subst) tys
        let reduced = List.map (fun qt -> contextReduceExn fresh qt.Context recEnv) norms
        ((zipWith (uncurry testAmbiguous) reduced norms), exps)
    
    let inferConstructorKinds fresh env (ctor: Syntax.Constructor) =
        let ctorVars = List.map Syntax.stypeFree (ctor.Result :: ctor.Components) |> Set.unionMany
        let kEnv = Set.fold (fun env v -> addTypeCtor env v (freshKind fresh)) env ctorVars
        let (kinds, constrs, tys) = map3 (kindInfer fresh kEnv) (List.append ctor.Components [ctor.Result])
        // every component in a constructor must be of kind data
        let valueConstrs = List.map (fun k -> { LeftKind = k; RightKind = KValue }) kinds
        kinds, List.append valueConstrs (List.concat constrs), tys

    let mkConstructorTy fresh componentsAndResult =
        let argTypes = List.take (List.length componentsAndResult - 1) componentsAndResult |> List.rev
        let retType = List.last componentsAndResult
        assert (List.forall (fun t -> typeKindExn t = KValue) argTypes)
        assert (typeKindExn retType = KValue)

        let rest = freshSequenceVar fresh
        let o = TSeq (DotSeq.ind retType rest)
        let i = TSeq (DotSeq.append (DotSeq.ofList argTypes) rest)
        let e = freshEffectVar fresh
        let p = freshPermVar fresh
        let fn = mkFunctionValueType e p totalAttr i o validAttr sharedAttr
        schemeFromQual (qualType [] fn)
    
    let inferRecDataTypes fresh env (dts : List<Syntax.DataType>) =
        let dataKindTemplate (dt : Syntax.DataType) = List.foldBack (fun _ k -> karrow (freshKind fresh) k) dt.Params KData
        let dataTypeKinds = List.map dataKindTemplate dts
        let recEnv =
            dataTypeKinds
            |> List.zip dts
            |> List.fold (fun e (dt, k) -> addTypeCtor e dt.Name.Name k) env
        let inferDataType (dt: Syntax.DataType) = List.map (inferConstructorKinds fresh recEnv) dt.Constructors
        let dtCtorKinds, constrs, dtCtorArgs =
            List.map (inferDataType >> List.unzip3) dts |> List.unzip3
        let subst = List.concat constrs |> List.concat |> solveKindConstraints
        let dataTypeKinds = List.map (kindSubst subst) dataTypeKinds
        let dtCtorArgs = List.map (List.map (List.map (typeKindSubstExn subst))) dtCtorArgs
        for kind in dataTypeKinds do
            if not (Set.isEmpty (kindFree kind))
            then
                failwith $"Polymorphic kinds not yet supported but inferred kind {kind}"
        let tyEnv =
            dataTypeKinds
            |> List.zip dts
            |> List.fold (fun env (dt, k) -> addTypeCtor env dt.Name.Name k) recEnv
        let ctorTypes = List.map (List.map (mkConstructorTy fresh)) dtCtorArgs
        let ctorNames = List.map (fun (dt: Syntax.DataType) -> List.map (fun (c: Syntax.Constructor) -> c.Name.Name) dt.Constructors) dts
        let ctorEnv =
            ctorTypes
            |> List.zip ctorNames
            |> List.collect (uncurry List.zip)
            |> List.fold (fun env p -> extendVar env (fst p) (snd p)) tyEnv
        ctorEnv
    
    let rec inferDefs fresh env defs exps =
        match defs with
        | [] -> (env, exps)
        | Syntax.DFunc f :: ds ->
            let (ty, exp) = inferFunction fresh env f
            inferDefs fresh (extendVar env f.Name.Name ty) ds (Syntax.DFunc exp :: exps)
        | Syntax.DRecFuncs fs :: ds ->
            let (tys, recExps) = inferRecFuncs fresh env fs
            let recFns = zipWith (fun (fn : Syntax.Function, exp) -> { fn with Body = exp }) fs recExps
            let newEnv =
                Syntax.declNames (Syntax.DRecFuncs fs)
                |> Syntax.namesToStrings
                |> Seq.zip (Seq.map (simplifyQual >> schemeFromQual) tys)
                |> Seq.fold (fun env nt -> extendVar env (snd nt) (fst nt)) env
            inferDefs fresh newEnv ds (Syntax.DRecFuncs recFns :: exps)
        | Syntax.DCheck c :: ds ->
            match lookup env c.Name.Name with
            | Some entry ->
                let general = instantiateExn fresh entry.Type
                let matcher = kindAnnotateQual fresh env c.Matcher
                // TODO: also check that the contexts match or are a subset
                if isTypeMatch fresh general.Head matcher.Head
                // TODO: should we continue to use the inferred (more general) type, or restrict it to
                // be the quantified asserted type?
                then inferDefs fresh env ds (Syntax.DCheck c :: exps)
                else failwith $"Type of '{c.Name}' did not match it's assertion.\n{general.Head} <> {matcher.Head}"
            | None -> failwith $"Could not find name '{c.Name}' to check its type."
        | Syntax.DEffect e :: ds ->
            // TODO: fix kind to allow effects with params here
            let effTyEnv = addTypeCtor env e.Name.Name KEffect
            let hdlrTys = List.map (fun (h: Syntax.HandlerTemplate) -> (h.Name.Name, schemeFromQual (kindAnnotateQual fresh effTyEnv h.Type))) e.Handlers
            let effEnv = Seq.fold (fun env nt -> extendVar env (fst nt) (snd nt)) effTyEnv hdlrTys
            inferDefs fresh effEnv ds (Syntax.DEffect e :: exps)
        | Syntax.DType d :: ds ->
            let dataTypeEnv = inferRecDataTypes fresh env [d]
            inferDefs fresh dataTypeEnv ds (Syntax.DType d :: exps)
        | Syntax.DRecTypes dts :: ds ->
            let dataTypeEnv = inferRecDataTypes fresh env dts
            inferDefs fresh dataTypeEnv ds (Syntax.DRecTypes dts :: exps)
        | Syntax.DTest t :: ds ->
            printfn $"Skipping type inference for test {t.Name.Name}, TI for tests will only run in test mode."
            inferDefs fresh env ds (Syntax.DTest t :: exps)
        | d :: ds -> failwith $"Inference for declaration {d} not yet implemented."
    
    let inferProgram prog =
        let fresh = SimpleFresh(0)
        let (env, expanded) = inferDefs fresh Primitives.primTypeEnv prog.Declarations []
        let (mType, mainExpand) = inferTop fresh env prog.Main
        // TODO: compile option for enforcing totality? right now we infer it but don't enforce it in any way
        // TODO: compile option for enforcing no unhandled effects? we infer them but don't yet check for this
        let mainTemplate = freshPush fresh (freshTotalVar fresh) (freshIntValueType fresh I32 (freshValidityVar fresh))
        if isTypeMatch fresh mainTemplate.Head mType.Head
        then { Declarations = expanded; Main = mainExpand }, env
        else failwith $"Main expected to have type {mainTemplate}, but had type {mType}"