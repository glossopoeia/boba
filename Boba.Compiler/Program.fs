namespace Boba.Compiler


module Main =

    open System
    open System.IO
    open FSharp.Text.Lexing

    [<EntryPoint>]
    let main argv =

        if argv.Length < 2
        then
            Console.WriteLine("Boba compiler expects 2 arguments!")
            Environment.Exit 1

        let env = Environment.CurrentDirectory
        // NOTE: all local import paths are relative to the directory of the main import file
        // TODO: determine whether this is really the right solution
        Environment.CurrentDirectory <- Path.GetDirectoryName(argv.[1])
        let mainModuleFileName = Path.GetFileNameWithoutExtension(argv.[1])
        let mainModulePath = Syntax.IPLocal { Value = $"\"{mainModuleFileName}\""; Position = Position.Empty }
        let program = UnitImport.loadProgram mainModulePath
        Environment.CurrentDirectory <- env

        let organized = UnitDependencies.organize program mainModulePath
        let maybeTests =
          if argv.[0] = "test"
          then TestGenerator.generateTestRunner organized
          elif argv.[0] = "compile"
          then TestGenerator.verifyHasMain organized
          else TestGenerator.emptyMain organized
        let renamed, startNames = Renamer.rename maybeTests
        let startNameStrings = List.map (fun (n : Syntax.Name) -> n.Name) startNames
        let isStartName n = List.contains n startNameStrings
        let expanded, typeEnv =
          try
            if argv.[0] = "no-types"
            then renamed, Boba.Core.Environment.empty
            else TypeInference.inferProgram renamed
          with
          | Boba.Core.Kinds.KindApplyArgMismatch (l, r) -> failwith $"Kind mismatch: {l} ~ {r}"

        if argv.[0] = "types"
        then
          Boba.Core.Environment.printEnv isStartName typeEnv
          Environment.Exit 0
        if argv.[0] = "types-all"
        then
          Boba.Core.Environment.printEnv (fun _ -> true) typeEnv
          Environment.Exit 0
        
        let condensed = Condenser.genCondensed expanded
        let core = CoreGen.genCoreProgram condensed
        let natives, blocks, constants = MochiGen.genProgram core

        GoOutputGen.writeAndRunDebug natives blocks constants