namespace Boba.Core

module Environment =

    open Common
    open Types
    open Kinds
    open CHR

    type EnvEntry = { Type: TypeScheme; IsOverload: bool; IsRecursive: bool; IsVariable: bool }

    type Overload = {
        Template: TypeScheme;
        Instances: List<TypeScheme * string>;
    }

    type TypeEnvironment = {
        Overloads: Map<string, Overload>;
        Rules: List<Rule>;
        Definitions: Map<string, EnvEntry>;
        TypeConstructors: Map<string, Kind>;
        Patterns: Map<string, TypeScheme>;
    }


    let empty = {
        Overloads = Map.empty;
        Rules = [];
        Definitions = Map.empty;
        TypeConstructors = Map.empty;
        Patterns = Map.empty
    }

    let envRules env : List<Rule> = env.Rules

    let addTypeCtor env name kind = { env with TypeConstructors = Map.add name kind env.TypeConstructors }

    let addPattern env name ty = { env with Patterns = Map.add name ty env.Patterns }

    let addOverload env name template insts = { env with Overloads = Map.add name { Template = template; Instances = insts } env.Overloads }

    let addRule env rule = { env with Rules = rule :: env.Rules }

    let extend env name entry = { env with Definitions = Map.add name entry env.Definitions }

    let extendVar env name ty = extend env name { Type = ty; IsOverload = false; IsRecursive = false; IsVariable = true; }

    let extendFn env name ty = extend env name { Type = ty; IsOverload = false; IsRecursive = false; IsVariable = false }

    let extendRec env name ty = extend env name { Type = ty; IsOverload = false; IsRecursive = true; IsVariable = false }

    let extendOver env name ty = extend env name { Type = ty; IsOverload = true; IsRecursive = true; IsVariable = false }

    let extendCtor env name pat ty = extendFn (addPattern env name pat) name ty

    let remove env name = { env with Definitions = (Map.remove name env.Definitions) }

    let lookup env name = env.Definitions.TryFind name

    let lookupType env name = env.TypeConstructors.TryFind name

    let lookupPattern env name = env.Patterns.TryFind name

    let printEnv env =
        Map.iter (fun n t -> printfn $"{n} : {t.Type}") env.Definitions
