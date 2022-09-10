namespace Boba.Compiler

/// Given a map of modules, the job of the dependency organizer is to arrange them such that
/// we can perform type inference of units as a basic fold, from left to right. This reduces
/// the need for state handling/checking of whether a declaration has been inferred during
/// inference; thanks to dependency organizing, we know that all dependencies of a given
/// declaration have already been checked.
module UnitDependencies =
    
    open Syntax

    
    type PathUnit = { Path: ImportPath; Unit: Unit }

    type OrganizedProgram = { Prims: List<Unit>; Units: List<PathUnit>; Main: PathUnit }



    let rec unitDependencies (program : Program) alreadySeen unit =
        let nonNativeImports = [for i in unitImports unit do if not i.Native then yield i]
        if not nonNativeImports.IsEmpty && List.forall (fun i -> List.contains i alreadySeen) nonNativeImports
        then failwith "Cyclical import detected"
        else 
            [for i in nonNativeImports ->
                List.append (unitDependencies program (i :: alreadySeen) program.Units.[i.Path]) [i.Path]]
            |> List.concat
            |> List.distinct

    /// Computes an in-order dependency tree-as-a-list for the whole program. Every unit has its
    /// dependencies names preceding it somewhere in the list.
    let dependencyList program = unitDependencies program [] program.Main

    /// Finds the first unit in the program with the given path name.
    let findUnit (program: OrganizedProgram) (path: ImportPath) =
        (List.find (fun (unit: PathUnit) -> unit.Path = path) program.Units).Unit

    /// Give a program with units that were loaded/stored in arbitrary order, compute the dependencies
    /// of the program and order the units from least dependent to most. The result is a program with
    /// a list of units where each unit is preceded by its dependencies. Circular units are not currently
    /// permitted.
    let organize (program : Syntax.Program) mainPath =
        { 
            Prims = program.Prims
            Units = [for d in dependencyList program -> { Path = d; Unit = program.Units.[d] }];
            Main = { Path = mainPath; Unit = program.Main }
        }