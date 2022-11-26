#!/usr/bin/env dotnet fsi

open System.Diagnostics
open System.Threading.Tasks

type CommandResult = { 
    ExitCode: int; 
    StandardOutput: string;
    StandardError: string 
}

let executeCommand executable args =
    task {
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

        do! p.WaitForExitAsync()
        let! out = outTask
        return {
            ExitCode = p.ExitCode;
            StandardOutput = out.[0];
            StandardError = out.[1]
        }
    }

let executeShellCommand command =
    executeCommand "/usr/bin/env" [ "-S"; "bash"; "-c"; command ]

let correctMainFiles = System.IO.Directory.GetFiles(".\\test\\correct-main", "*.boba")
let correctTestFiles = System.IO.Directory.GetFiles(".\\test\\correct-test", "*.boba")
let wrongFiles = System.IO.Directory.GetFiles(".\\test\\wrong", "*.boba")

let expectCorrect test file =
    executeCommand "dotnet" ["run"; "--project"; "Boba.Compiler"; test; file]

let expectCorrectMain test cmp file =
    task {
        printfn $"Running test '{file}'"
        let! runRes = expectCorrect test file
        if cmp runRes.ExitCode 0
        then
            printfn $"Test '{file}' failed"
            return 1
        else return 0
    }

let sumAsyncInt (tasks: List<Task<int>>) =
    task {
        let! ints = Task.WhenAll tasks
        return Seq.sum ints
    }

let res = task {
    let! mainRes = sumAsyncInt [for f in correctMainFiles -> expectCorrectMain "run" (<>) f]
    let! testRes = sumAsyncInt [for f in correctTestFiles -> expectCorrectMain "test" (<>) f]
    let! wrongRes = sumAsyncInt [for f in wrongFiles -> expectCorrectMain "test" (=) f]
    return mainRes + testRes + wrongRes
}

Async.RunSynchronously (Async.AwaitTask res)