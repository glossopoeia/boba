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

let testPath p = System.IO.Path.Combine(".", "test", p)

let correctMainFiles = System.IO.Directory.GetFiles(testPath "correct-main", "*.boba")
let correctTestFiles = System.IO.Directory.GetFiles(testPath "correct-test", "*.boba")
let wrongFiles = System.IO.Directory.GetFiles(testPath "wrong", "*.boba")

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
        else
            printfn $"Test '{file}' succeeded"
            return 0
    }

let batchesOf n =
    let mutable i = -1
    List.groupBy (fun _ -> i <- i + 1; i / n) >> Seq.map snd

let sumAsyncInt (tasks: List<unit -> Task<int>>) =
    task {
        let batches = batchesOf 7 tasks
        let mutable sum = 0
        for b in batches do
            let! ints = Task.WhenAll [for t in b -> t ()]
            sum <- sum + Array.sum ints
        return sum
    }

let res = task {
    let! mainRes = sumAsyncInt [for f in correctMainFiles -> fun () -> expectCorrectMain "run" (<>) f]
    let! testRes = sumAsyncInt [for f in correctTestFiles -> fun () -> expectCorrectMain "test" (<>) f]
    let! wrongRes = sumAsyncInt [for f in wrongFiles -> fun () -> expectCorrectMain "test" (=) f]
    return mainRes + testRes + wrongRes
}

Async.RunSynchronously (Async.AwaitTask res)
|> System.Environment.Exit