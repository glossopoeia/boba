namespace Boba.Core

module Environment =

    open Common
    open Types
    open Kinds
    open Declarations

    type EnvEntry = { Type: TypeScheme; IsClassMethod: bool; IsRecursive: bool; IsVariable: bool }

    type TypeEnvironment = {
        Classes: Map<string, Typeclass>;
        Definitions: Map<string, EnvEntry>;
        TypeConstructors: Map<string, Kind>;
        Patterns: Map<string, TypeScheme>;
    }


    let empty = { Classes = Map.empty; Definitions = Map.empty; TypeConstructors = Map.empty; Patterns = Map.empty }

    let addTypeCtor env name kind = { env with TypeConstructors = Map.add name kind env.TypeConstructors }

    let addPattern env name ty = { env with Patterns = Map.add name ty env.Patterns }

    let extend env name entry = { env with Definitions = Map.add name entry env.Definitions }

    let extendVar env name ty = extend env name { Type = ty; IsClassMethod = false; IsRecursive = false; IsVariable = true; }

    let extendRec env name ty = extend env name { Type = ty; IsClassMethod = false; IsRecursive = true; IsVariable = false }

    let extendCtor env name pat ty = extendVar (addPattern env name pat) name ty

    let remove env name = { env with Definitions = (Map.remove name env.Definitions) }

    let lookup env name = env.Definitions.TryFind name

    let lookupType env name = env.TypeConstructors.TryFind name

    let lookupPattern env name = env.Patterns.TryFind name

    let lookupClass env className = env.Classes.TryFind(className)

    let lookupClassByMethod (env : TypeEnvironment) methodName =
        Map.tryPick (fun k v -> if v.Methods.ContainsKey methodName then Some v else None) env.Classes

    let printEnv env =
        Map.iter (fun n t -> printfn $"{n} : {t.Type}") env.Definitions
