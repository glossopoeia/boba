namespace Boba.Compiler

module UnitImport =

    open System
    open System.IO
    open System.Net.Http
    open FSharp.Text.Lexing
    open Syntax

    let getCachedRemote remotePath =
        let r = remotePath
        let cacheFolder = Path.Combine ("boba-pearls", $"{r.Org.Name}.{r.Project.Name}.{r.Unit.Name}.{r.Major.Value}.{r.Minor.Value}.{r.Patch.Value}")
        let cacheFolderPath = Path.Combine (Path.GetTempPath (), cacheFolder)
        Directory.CreateDirectory cacheFolderPath

        let cacheFilePath = Path.Combine (cacheFolderPath, $"unit.boba")
        if not (File.Exists cacheFilePath)
        then
            printfn $"Module {IPRemote r} not cached, downloading..."
            let url = $"https://raw.github.com/{r.Org.Name}/{r.Project.Name}/{r.Major.Value}.{r.Minor.Value}.{r.Patch.Value}/{r.Unit.Name}.boba"
            try
                let content = (new HttpClient()).GetStringAsync(url) |> Async.AwaitTask |> Async.RunSynchronously
                try
                    File.WriteAllText (cacheFilePath, content)
                with
                    ex -> printfn $"Failed to cache {IPRemote r} with {ex}"
                content
            with
                _ -> failwith $"Import {IPRemote r} could not be located at {url}."
        else
            File.ReadAllText cacheFilePath

    let getModuleText modulePath =
        match modulePath with
        | IPLocal local ->
            let fileName = local.Value.Substring(1, (local.Value.Length - 2))
            File.ReadAllText $"{fileName}.boba"
        | IPRemote name -> getCachedRemote name

    let parseModule modulePath buffer =
        try
            Parser.unit Lexer.token buffer
        with e ->
            failwith $"Parse failed in '{modulePath}' at: {buffer.EndPos.Line}, {buffer.EndPos.Column}\n    with '{String(buffer.Lexeme)}'"

    let loadModule path =
        getModuleText path
        |> LexBuffer<char>.FromString
        |> parseModule path

    let rec loadDependencies alreadySeen imports loaded =
        match imports with
        | [] -> loaded
        | i :: is ->
            if not (List.contains i alreadySeen)
            then
                let load = loadModule i
                let newImps = [for i in unitImports load do if not i.Native then yield i.Path]
                loadDependencies (i :: alreadySeen) (List.append is newImps) (Map.add i load loaded)
            else loadDependencies alreadySeen is loaded

    let loadProgram primTexts entryPath =
        let primAsts = Seq.map (fun p -> parseModule (fst p) (LexBuffer<char>.FromString (snd p))) primTexts
        let start = loadModule entryPath
        let imports = [for i in unitImports start do if not i.Native then yield i.Path]
        let deps = loadDependencies [entryPath] imports Map.empty
        { Prims = List.ofSeq primAsts; Units = deps; Main = start }