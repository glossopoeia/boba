namespace Boba.Compiler


module Main =

    open System
    open System.IO
    open FSharp.Text.Lexing
    open UnitImport
    open Syntax

    let infoMain args =
      printfn "Usage: boba [command] [command-options] [arguments]"
      printfn ""
      printfn "Execute a Boba compiler command."
      printfn ""
      printfn "Commands:"
      printfn "  build          Build a Boba program from a source file with an entry point."
      printfn "  run            Build and run a Boba program from a source file with an entry point."
      printfn "  test           Run user-written tests and laws to verify code behavior."
      printfn "  publish        Publish a new or updated Boba pearl to https://pearls.tech."
      printfn "  clean          Clean build outputs and dependencies of a Boba program."
      printfn "  docs           Generate Markdown documentation from a Boba source file."
      printfn "  format         Apply code style preferences to a Boba source file."
      printfn "  tree           Generate a recursive map of the dependencies of a Boba source file."
      printfn ""
      printfn "Run 'boba [command] --help' for more information on a command."
      0
    
    let loadFromMain (shortPath: string) =
      let env = Environment.CurrentDirectory
      let currDir = Path.GetDirectoryName(shortPath)
      if not (String.IsNullOrEmpty currDir)
      then Environment.CurrentDirectory <- currDir
      let mainModuleFileName = Path.GetFileNameWithoutExtension(shortPath)
      let mainModulePath = Syntax.IPLocal { Value = $"\"{mainModuleFileName}\""; Position = Position.Empty }
      let program = loadProgram mainModulePath
      Environment.CurrentDirectory <- env
      printfn $"Loading complete!"
      program, mainModulePath
    
    let loadWithMain mainFn shortPath =
      let program, mainModulePath = loadFromMain shortPath
      let organized = UnitDependencies.organize program mainModulePath
      let withTransformedMain = mainFn organized
      let renamed, startNames = Renamer.rename withTransformedMain
      printfn $"Renaming complete!"
      let expanded, typeEnv = TypeInference.inferProgram renamed
      printfn $"Type inference complete!"
      expanded, typeEnv, startNames

    let buildMain (args: string array) =
      // optionally compile with no debug output trace
      let isInspect = Seq.exists (fun arg -> arg = "--inspect" || arg = "-i") args

      let expanded, typeEnv, startNames = loadWithMain TestGenerator.verifyHasMain args.[0]
      let condensed = Condenser.genCondensed expanded typeEnv
      let core = CoreGen.genCoreProgram condensed
      printfn $"Core generation complete!"
      let natives, blocks, constants = MochiGen.genProgram core
      printfn $"Bytecode generation complete!"
      GoOutputGen.writeAndBuildDebug natives blocks constants isInspect
    
    let runMain (args: string array) =
      // optionally compile with no debug output trace
      let buildRes = buildMain args
      if buildRes = 0
      then GoOutputGen.runBuild ()
      else buildRes
    
    let testMain (args: string array) =
      let isInspect = false

      let expanded, typeEnv, startNames = loadWithMain TestGenerator.generateTestRunner args.[0]
      let condensed = Condenser.genCondensed expanded typeEnv
      let core = CoreGen.genCoreProgram condensed
      printfn $"Core generation complete!"
      let natives, blocks, constants = MochiGen.genProgram core
      printfn $"Bytecode generation complete!"
      let buildRes = GoOutputGen.writeAndBuildDebug natives blocks constants isInspect
      if buildRes = 0
      then GoOutputGen.runBuild ()
      else buildRes
    
    let docsMain (args: string array) =
      let expanded, typeEnv, startNames = loadWithMain TestGenerator.emptyMain args.[0]
      let startNameStrings = List.map (fun (n : Syntax.Name) -> n.Name) startNames
      let isStartName n = List.contains n startNameStrings

      let fresh = Boba.Core.Fresh.SimpleFresh(0)
      let simplifier ty =
        if Boba.Core.Types.isQualType ty
        then TypeInference.contextReduceExn fresh ty typeEnv.Classes |> snd
        else ty

      //if argv.[0] = "types"
      //then
      //  Boba.Core.Environment.printEnv isStartName simplifier typeEnv
      //  Environment.Exit 0
      //if argv.[0] = "types-all"
      //then
      //  Boba.Core.Environment.printEnv (fun _ -> true) simplifier typeEnv
      //  Environment.Exit 0
      //if argv.[0] = "docs"
      //then
      let docs = Documentation.generate args.[0] isStartName simplifier typeEnv expanded.Declarations
      File.WriteAllText ("docs.md", docs)
      0
    
    let formatMain args =
      printfn "Format command is not yet implemented. Check https://github.com/glossopoeia/boba/issues for updates."
      0

    let publishMain args =
      printfn "Publish command is not yet implemented. Check https://github.com/glossopoeia/boba/issues for updates."
      0
    
    let treeMain args =
      printfn "Tree command is not yet implemented. Check https://github.com/glossopoeia/boba/issues for updates."
      0
    
    let cleanMain args =
      printfn "Clean command is not yet implemented. Check https://github.com/glossopoeia/boba/issues for updates."
      0
    
    [<EntryPoint>]
    let main argv =

        if argv.Length < 1
        then
          printfn "Boba compiler expects a command. Type 'boba info' for a list of commands."
          1
        else
          let rest = Array.tail argv
          match argv.[0] with
          | "info" -> infoMain rest
          | "build" -> buildMain rest
          | "run" -> runMain rest
          | "test" -> testMain rest
          | "docs" -> docsMain rest
          | "publish" -> publishMain rest
          | "format" -> formatMain rest
          | "tree" -> treeMain rest
          | "clean" -> cleanMain rest
          | _ ->
            printfn $"Unknown command '{argv.[0]}'. Type 'boba info' for a list of commands."
            1