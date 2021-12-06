namespace Boba.Core

module Environment =

    open Common
    open Types
    open Declarations

    type EnvEntry = { Type: TypeScheme; IsClassMethod: bool; IsRecursive: bool }

    type TypeEnvironment = { Classes: Map<string, Typeclass>; Definitions: Map<string, EnvEntry> }


    let empty = { Classes = Map.empty; Definitions = Map.empty }

    let extend env name entry = { env with Definitions = (Map.add name entry env.Definitions) }

    let extendVar env name ty = extend env name { Type = ty; IsClassMethod = false; IsRecursive = false; }

    let remove env name = { env with Definitions = (Map.remove name env.Definitions) }

    let lookup env name = env.Definitions.TryFind name

    let lookupClass env className = env.Classes.TryFind(className)

    let lookupClassByMethod (env : TypeEnvironment) methodName =
        Map.tryPick (fun k v -> if v.Methods.ContainsKey methodName then Some v else None) env.Classes
