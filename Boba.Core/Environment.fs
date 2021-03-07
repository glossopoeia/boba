namespace Boba.Core

module Environment =

    open Common
    open Types

    type TypeEnvironment = { Adhocs: Map<string, List<QualifiedType>>; Definitions: Map<string, TypeScheme> }


    let empty = { Adhocs = Map.empty; Definitions = Map.empty }

    let extend env name scheme = { env with Definitions = (Map.add name scheme env.Definitions) }

    let remove env name = { env with Definitions = (Map.remove name env.Definitions) }

    let lookup env name = env.Definitions.TryFind name

    let lookupClass env className = env.Adhocs.TryFind(className)

    let addClass env name =
        match lookupClass env name with
        | Some _ -> failwith $"Typeclass {name} already exists in environment"
        | None -> { env with Adhocs = env.Adhocs.Add(name, []) }

    let modifyClass env name insts = { env with Adhocs = env.Adhocs.Change(name, constant insts) }
