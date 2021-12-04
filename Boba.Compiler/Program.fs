namespace Boba.Compiler


module Main =

    open System
    open System.Diagnostics
    open System.IO
    open System.Threading.Tasks
    open FSharp.Text.Lexing
    open Mochi.Simulator

    type CommandResult = { 
      ExitCode: int; 
      StandardOutput: string;
      StandardError: string 
    }

    let executeCommand executable args =
      async {
        let startInfo = ProcessStartInfo()
        startInfo.FileName <- executable
        for a in args do
          startInfo.ArgumentList.Add(a)
        startInfo.RedirectStandardOutput <- true
        startInfo.RedirectStandardError <- true
        startInfo.UseShellExecute <- false
        startInfo.CreateNoWindow <- true
        use p = new Process()
        p.StartInfo <- startInfo
        p.Start() |> ignore

        let outTask = Task.WhenAll([|
          p.StandardOutput.ReadToEndAsync();
          p.StandardError.ReadToEndAsync()
        |])

        do! p.WaitForExitAsync() |> Async.AwaitTask
        let! out = outTask |> Async.AwaitTask
        return {
          ExitCode = p.ExitCode;
          StandardOutput = out.[0];
          StandardError = out.[1]
        }
      }

    let executeShellCommand command =
      executeCommand "/usr/bin/env" [ "-S"; "bash"; "-c"; command ]

    let rec copyDirRec src dest =
        if not <| System.IO.Directory.Exists(dest) then
            System.IO.Directory.CreateDirectory(dest) |> ignore

        let srcDir = DirectoryInfo(src)

        for file in srcDir.GetFiles() do
            let temppath = System.IO.Path.Combine(dest, file.Name)
            file.CopyTo(temppath, true) |> ignore

        for subdir in srcDir.GetDirectories() do
            let dstSubDir = System.IO.Path.Combine(dest, subdir.Name)
            copyDirRec subdir.FullName dstSubDir

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
        let program = UnitImport.loadProgram (Syntax.IPLocal { Value = $"\"{mainModuleFileName}\""; Position = Position.Empty })
        Environment.CurrentDirectory <- env

        let organized = UnitDependencies.organize program
        let maybeTests =
          if argv.[0] = "test"
          then TestGenerator.generateTestRunner organized
          else TestGenerator.verifyHasMain organized
        let renamed = Renamer.rename maybeTests
        let condensed = Condenser.genCondensed renamed
        let core = CoreGen.genCoreProgram condensed
        let mochi = MochiGen.genProgram core

        copyDirRec "./mochivm" "./output"

        let sw = new StreamWriter("./output/main.c")
        BytecodeGen.writeBlocks sw (fst mochi) (snd mochi)
        sw.Flush()

        Environment.CurrentDirectory <- "./output"
        Console.WriteLine("Switched directory {0}", Environment.CurrentDirectory)

        let exeRes = executeShellCommand "make MODE=debug" |> Async.RunSynchronously
        if exeRes.ExitCode <> 0
        then
            eprintfn "%s" exeRes.StandardError
            Environment.Exit 1
        else printfn "%s" exeRes.StandardOutput
        Console.WriteLine("application build successful")

        let runRes = executeShellCommand "./build/debug/mochivm" |> Async.RunSynchronously
        if runRes.ExitCode = 0
        then
            printfn "%s" runRes.StandardOutput
            printfn "App ran successfully"
        else
            printfn "%s" runRes.StandardError
            printfn "App run failed"

        //let initial = Machine.newMachine mochi
        //let result = Evaluation.run initial

        //Console.WriteLine(result.Stack)
        runRes.ExitCode