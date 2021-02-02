namespace Boba.Core

module Environment =

    open Kinds
    open Types

    type EnvironmentEntry =
        | ETypeVarIntro of string * Kind
        | ETypeVarDef of string * Type
        | ETermVarBind of string * TypeScheme
        | ELocalityMark
        | ETypeClassDecl of className: string * instances: List<TypeScheme>
        | ETypeConstraint of left: Type * right: Type
        | EFlexFlexConstraint of left: string * right: string * kind: Kind
        | EFlexRigidHullConstraint of var: string * kind: Kind * rigid: Type * dependencies: List<EnvironmentEntry>
        | EUnitConstraint of unit: Abelian.Equation<string, string> * dependency: Option<string>
        | EFixedConstraint of fix: Abelian.Equation<string, int> * dependency: Option<string>
        | EBooleanConstraint of eqn: Boolean.Equation
        | ERowConstraint of leftFields: List<(string*Type)> * rightFields: List<(string*Type)> * leftRow: Type * rightRow: Type
        | ESeqConstraint of left: DotSeq.DotSeq<Type> * right: DotSeq.DotSeq<Type>
        | ESubstConstraint of subst: Map<string, Type> * dependencies: List<EnvironmentEntry>


    // utilities for working with environment entries
    let typeVarIntro name kind = ETypeVarIntro (name, kind)

    let typeVarDef name def = ETypeVarDef (name, def)

    let termVarBind name ty = ETermVarBind (name, ty)

    let typeClass name insts = ETypeClassDecl (name, insts)

    let simpleBinaryConstr left right = ETypeConstraint (left, right)

    let flexFlexConstr left right kind = EFlexFlexConstraint (left, right, kind)

    let flexRigidConstr var kind rigid deps = EFlexRigidHullConstraint (var, kind, rigid, deps)

    let simpleUnitConstr unit dep = EUnitConstraint (unit, dep)
    
    let binaryUnitConstr (left: Abelian.Equation<string, string>) right = EUnitConstraint (left.Subtract(right), None)
    
    let binaryUnitConstrDep (left: Abelian.Equation<string, string>) right deps = EUnitConstraint (left.Subtract(right), Some deps)

    let rowConstr lefts rights lr rr = ERowConstraint (lefts, rights, lr, rr)
    
    let fieldsToRowConstr leftRow rightRow =
        let rec typeRowToConstraintRow acc tyrow =
            match tyrow with
            | TField (f, a, r) -> typeRowToConstraintRow ((f,a) :: acc) r
            | _ -> (acc, tyrow)
        let (leftFields, leftRow) = typeRowToConstraintRow [] leftRow
        let (rightFields, rightRow) = typeRowToConstraintRow [] rightRow
        ERowConstraint (leftFields, rightFields, leftRow, rightRow)
    
    let rec rowConstrSideToField fields rowEnd =
        match fields with
        | (f, a) :: fs -> typeField f a (rowConstrSideToField fs rowEnd)
        | [] -> rowEnd

    let seqConstr left right = ESeqConstraint (left, right)
    
    let substConstr subst deps = ESubstConstraint (subst, deps)

    let binaryBooleanConstr left right = EBooleanConstraint (Boolean.simplify (Boolean.BOr (Boolean.BAnd (Boolean.BNot left, right), Boolean.BAnd(left, Boolean.BNot right))))

    let isConstraint entry =
        match entry with
        | ETypeConstraint _ -> true
        | EFlexFlexConstraint _ -> true
        | EFlexRigidHullConstraint _ -> true
        | EUnitConstraint _ -> true
        | EFixedConstraint _ -> true
        | EBooleanConstraint _ -> true
        | ERowConstraint _ -> true
        | ESeqConstraint _ -> true
        | ESubstConstraint _ -> true
        | _ -> false

    let isLocalityMark entry =
        match entry with
        | ELocalityMark -> true
        | _ -> false

    let typeVarName entry =
        match entry with
        | ETypeVarIntro (n, _) -> n
        | ETypeVarDef (n, _) -> n
        | _ -> failwith "Expected a type variable entry"

    let constraintFields fields = List.map fst fields |> Set.ofList
    
    let sharedConstraintFields lefts rights = Set.intersect (constraintFields lefts) (constraintFields rights)


    // substitution computations
    let applyEntryTypeExn t entry =
        match entry with
        | ETypeVarDef (n, def) -> typeSubstExn n def t
        | _ -> t

    let applyEnvTypeExn env t = List.fold applyEntryTypeExn t env

    let applyEnvPredExn env p = { Name = p.Name; Argument = applyEnvTypeExn env p.Argument }

    let applyEnvQualExn env q = { Context = List.map (applyEnvPredExn env) q.Context; Head = applyEnvTypeExn env q.Head }


    // type class utilities
    let rec findClass name env =
        match env with
        | ETypeClassDecl (n, insts) :: _ when n = name -> Some (n, insts)
        | _ :: es -> findClass name es
        | [] -> None

    let addClass name env =
        match findClass name env with
        | Some _ -> failwith $"Typeclass {name} already exists in environment"
        | None -> ETypeClassDecl (name, []) :: env

    let rec modifyClass name insts env =
        match env with
        | ETypeClassDecl (n, is) :: es when n = name -> ETypeClassDecl (name, insts) :: es
        | e :: es -> e :: modifyClass name insts es
        | [] -> []


    // predicate head normal form
    let getInstanceSubgoals pred env =
        match findClass pred.Name env with
        | Some (_, insts) ->
            let matching = List.filter (fun i -> isTypeMatch i.Body.Head pred.Argument) insts
            if List.isEmpty matching
            then None
            else
                let first = List.head matching
                typeMatch first.Body.Head pred.Argument
                |> Option.map (fun subst -> applySubstContext subst first.Body.Context)
        | None -> failwith "Could not find type class"

    let rec toHeadNormalForm pred env =
        if predHeadNoramlForm pred
        then [pred]
        else
            match getInstanceSubgoals pred env with
            | Some subgoals -> [for sub in subgoals do yield toHeadNormalForm sub env] |> List.concat
            | None -> failwith "Context reduction failed"


    // context operations
    let rec predEntails pred env =
        match getInstanceSubgoals pred env with
        | Some subgoals -> List.forall (fun sub -> predEntails sub env) subgoals
        | None -> false

    let contextToHeadNormalForm context env = List.map (fun p -> toHeadNormalForm p env) context |> List.concat

    let contextSimplify env context =
        let mutable simplified = []
        let mutable remaining = context
        while not (List.isEmpty remaining) do
            let test :: rest = remaining
            if not (predEntails test env)
            then simplified <- test :: simplified
            remaining <- rest
        simplified

    let contextReduce context env = contextToHeadNormalForm context env |> contextSimplify env


    // accessors over contexts
    let rec getTermVarType var env =
        match env with
        | ETermVarBind (n, t) :: _ when n = var -> Option.Some t
        | _ :: cs -> getTermVarType var cs
        | [] -> Option.None

    
    // other utilities
    let makeScheme generalized ty =
        let mutable body = ty
        let mutable quantified = List.empty
        for g in generalized do
            match g with
            | ETypeVarIntro (n, k) -> quantified <- (n, k) :: quantified
            | ETypeVarDef (n, d) -> body <- qualSubstExn n d body
            | _ -> failwith "Unexpected entry in skimmed context"
        schemeType quantified body

    let normalizeEntry env entry =
        match entry with
        | ETypeVarDef (n, t) -> ETypeVarDef (n, applyEnvTypeExn env t)
        | _ -> entry

    let normalizeEnv = List.fold (fun prev next -> normalizeEntry prev next :: prev) []