namespace Boba.Compiler

/// Given a map of modules, the job of the dependency organizer is to arrange them such that
/// we can perform type inference of units as a basic fold, from left to right. This reduces
/// the need for state handling/checking of whether a declaration has been inferred during
/// inference; thanks to dependency organizing, we know that all dependencies of a given
/// declaration have already been checked.
module UnitDependencies =
    
    open Syntax

    
    type PathUnit = { Path: ImportPath; Unit: Unit }

    type OrganizedProgram = { Units: List<PathUnit>; Main: Unit }



    let rec unitDependencies (program : Program) alreadySeen unit =
        let imps = unitImports unit
        if not imps.IsEmpty && List.forall (fun i -> List.contains i alreadySeen) imps
        then failwith "Cyclical import detected"
        else 
            [for i in imps -> List.append (unitDependencies program (i :: alreadySeen) program.Units.[i.Path]) [i.Path]]
            |> List.concat
            |> List.distinct

    let dependencyList program = unitDependencies program [] program.Main

    let organize program =
        { 
            Units = [for d in dependencyList program -> { Path = d; Unit = program.Units.[d] }];
            Main = program.Main
        }