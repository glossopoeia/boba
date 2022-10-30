namespace Boba.Compiler


module Main =

    open System
    open System.IO
    open FSharp.Text.Lexing
    open UnitImport
    open Syntax

    [<EntryPoint>]
    let main argv =

        if argv.Length < 2
        then
            Console.WriteLine("Boba compiler expects 2 arguments!")
            Environment.Exit 1

        let env = Environment.CurrentDirectory

        // optionally compile with no debug output trace
        let isDebug =
          if argv.Length >= 3 && argv.[2] = "release"
          then false
          else true

        Environment.CurrentDirectory <- Path.GetDirectoryName(argv.[1])
        let mainModuleFileName = Path.GetFileNameWithoutExtension(argv.[1])
        let mainModulePath = Syntax.IPLocal { Value = $"\"{mainModuleFileName}\""; Position = Position.Empty }
        let program = loadProgram mainModulePath
        printfn $"Loading complete!"
        Environment.CurrentDirectory <- env

        let organized = UnitDependencies.organize program mainModulePath
        let maybeTests =
          if argv.[0] = "test"
          then TestGenerator.generateTestRunner organized
          elif argv.[0] = "compile"
          then TestGenerator.verifyHasMain organized
          else TestGenerator.emptyMain organized
        let renamed, startNames = Renamer.rename maybeTests
        printfn $"Renaming complete!"
        let startNameStrings = List.map (fun (n : Syntax.Name) -> n.Name) startNames
        let isStartName n = List.contains n startNameStrings
        let expanded, typeEnv =
          try
            if argv.[0] = "no-types"
            then renamed, Boba.Core.Environment.empty
            else TypeInference.inferProgram renamed
          with
          | Boba.Core.Kinds.KindApplyArgMismatch (l, r) -> failwith $"Kind mismatch: {l} ~ {r}"
        printfn $"Type inference complete!"

        let fresh = Boba.Core.Fresh.SimpleFresh(0)
        let simplifier ty =
          if Boba.Core.Types.isQualType ty
          then TypeInference.contextReduceExn fresh ty typeEnv.Classes |> snd
          else ty

        if argv.[0] = "types"
        then
          Boba.Core.Environment.printEnv isStartName simplifier typeEnv
          Environment.Exit 0
        if argv.[0] = "types-all"
        then
          Boba.Core.Environment.printEnv (fun _ -> true) simplifier typeEnv
          Environment.Exit 0
        if argv.[0] = "docs"
        then
          let docs = Documentation.generate argv.[1] isStartName simplifier typeEnv expanded.Declarations
          File.WriteAllText ("docs.md", docs)
          Environment.Exit 0
        
        let condensed = Condenser.genCondensed expanded typeEnv
        let core = CoreGen.genCoreProgram condensed
        printfn $"Core generation complete!"
        let natives, blocks, constants = MochiGen.genProgram core
        printfn $"Bytecode generation complete!"

        GoOutputGen.writeAndRunDebug natives blocks constants isDebug