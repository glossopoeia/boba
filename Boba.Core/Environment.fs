namespace Boba.Core

module Environment =

    open Common
    open Types
    open Kinds
    open CHR

    type EnvEntry = { Type: TypeScheme; IsOverload: bool; IsRecursive: bool; IsVariable: bool }

    type Overload = {
        Pred: string;
        Template: TypeScheme;
        Instances: List<TypeScheme * string>;
        Params: List<string>;
    }

    type TypeEnvironment = {
        Overloads: Map<string, Overload>;
        Rules: List<Rule>;
        Classes: List<Rule>;
        Definitions: Map<string, EnvEntry>;
        Kinds: Map<string, UnifySort>;
        TypeConstructors: Map<string, KindScheme>;
        TypeSynonyms: Map<string, TypeScheme>;
        Patterns: Map<string, TypeScheme>;
    }


    let empty = {
        Overloads = Map.empty;
        Rules = [];
        Classes = [];
        Definitions = Map.empty;
        Kinds = Map.empty;
        TypeConstructors = Map.empty;
        TypeSynonyms = Map.empty;
        Patterns = Map.empty
    }

    let envRules env : List<Rule> = env.Rules

    let addTypeCtor env name kind = { env with TypeConstructors = Map.add name kind env.TypeConstructors }

    let addUserKind env name unify = { env with Kinds = Map.add name unify env.Kinds }

    let addPattern env name ty = { env with Patterns = Map.add name ty env.Patterns }

    let addOverload env name pred template pars insts = { env with Overloads = Map.add name { Pred = pred; Template = template; Instances = insts; Params = pars } env.Overloads }

    let addRule env rule = { env with Rules = rule :: env.Rules }

    let addClass env classRule = { env with Classes = classRule :: env.Classes }

    let addSynonym env name scheme = { env with TypeSynonyms = Map.add name scheme env.TypeSynonyms }

    let extend env name entry = { env with Definitions = Map.add name entry env.Definitions }

    let extendVar env name ty = extend env name { Type = ty; IsOverload = false; IsRecursive = false; IsVariable = true; }

    let extendFn env name ty = extend env name { Type = ty; IsOverload = false; IsRecursive = false; IsVariable = false }

    let extendRec env name ty = extend env name { Type = ty; IsOverload = false; IsRecursive = true; IsVariable = false }

    let extendOver env name ty = extend env name { Type = ty; IsOverload = true; IsRecursive = true; IsVariable = false }

    let extendCtor env name pat ty = extendFn (addPattern env name pat) name ty

    let remove env name = { env with Definitions = (Map.remove name env.Definitions) }

    let lookup env name = env.Definitions.TryFind name

    let lookupType env name = env.TypeConstructors.TryFind name

    let lookupKind env name = env.Kinds.TryFind name

    let lookupPattern env name = env.Patterns.TryFind name

    let lookupPred env name = Seq.find (fun over -> over.Pred = name) (Map.values env.Overloads)

    let lookupSynonym env name = env.TypeSynonyms.TryFind name

    let printEnv nameFilter simplifier env =
        Map.filter (fun n t -> nameFilter n) env.Definitions
        |> Map.iter (fun n t -> printfn $"{n} : {prettyType (simplifier t.Type.Body)}")
        Map.filter (fun n o -> nameFilter n) env.Overloads
        |> Map.iter (fun n o ->
            printfn $"{n} : {prettyType o.Template.Body}"
            Seq.iter (fun (t : TypeScheme, n) -> printfn $"{n} : {prettyType t.Body}") o.Instances)
