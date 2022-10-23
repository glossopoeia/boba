namespace Boba.Compiler

module UnitImport =

    open System
    open System.IO
    open System.Net.Http
    open FSharp.Text.Lexing
    open Syntax

    let remotePathToUrl r =
        $"https://raw.github.com/{r.Org.Name}/{r.Project.Name}/{r.Major.Value}.{r.Minor.Value}.{r.Patch.Value}/{r.Unit.Name}.boba"

    let getCachedRemote remotePath =
        let r = remotePath
        let cacheFolder = Path.Combine ("boba-pearls", $"{r.Org.Name}.{r.Project.Name}.{r.Unit.Name}.{r.Major.Value}.{r.Minor.Value}.{r.Patch.Value}")
        let cacheFolderPath = Path.Combine (Path.GetTempPath (), cacheFolder)
        Directory.CreateDirectory cacheFolderPath |> ignore

        let cacheFilePath = Path.Combine (cacheFolderPath, $"unit.boba")
        if not (File.Exists cacheFilePath)
        then
            printfn $"Module {IPRemote r} not cached, downloading..."
            let url = remotePathToUrl r
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
        | IPLocal _ -> File.ReadAllText $"{modulePath}.boba"
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

    let makeAbsolutePathTo parent path =
        match path with
        | IPLocal _ ->
            match parent with
            | IPLocal l -> IPLocal { l with Value = "\"" + $"""{(Path.Combine(Path.GetDirectoryName($"{parent}"), $"{path}"))}""" + "\"" }
            | IPRemote r -> IPRemote { r with Unit = { r.Unit with Name = $"{path}" } }
        | IPRemote _ -> path
    
    let injectCoreImport imps =
        List.append imps [{
            Native = false
            Unaliased = IUAll
            Alias = stringToSmallName ""
            Path = IPRemote { 
                Org = stringToSmallName "glossopoeia"
                Project = stringToSmallName "boba-core"
                Unit = stringToSmallName "core"
                Major = intToLiteral "0"
                Minor = intToLiteral "0"
                Patch = intToLiteral "11"
            } }]

    let rec loadDependencies alreadySeen imports loaded =
        match imports with
        | [] -> loaded
        | i :: is ->
            if not (List.contains i alreadySeen)
            then
                let load = loadModule i
                let absolutePathImports =
                    [
                        for sub in unitImports load ->
                            if not sub.Native
                            then { sub with Path = makeAbsolutePathTo i sub.Path }
                            else sub
                    ]
                let imports =
                    match i with
                    | IPRemote { Org = o; Project = p } when o.Name = "glossopoeia" && p.Name = "boba-core" ->
                        absolutePathImports
                    | _ -> injectCoreImport absolutePathImports
                let load = unitSetImports load imports
                let newImps = [for subI in unitImports load do if not subI.Native then yield subI.Path]
                loadDependencies (i :: alreadySeen) (List.append is newImps) (Map.add i load loaded)
            else
                loadDependencies alreadySeen is loaded

    let loadProgram entryPath =
        let start = loadModule entryPath
        let absolutePathImports =
            [
                for i in unitImports start ->
                    if not i.Native
                    then { i with Path = makeAbsolutePathTo entryPath i.Path }
                    else i
            ]
        let start = unitSetImports start (injectCoreImport absolutePathImports)
        let imports = [for i in unitImports start do if not i.Native then yield i.Path]
        let deps = loadDependencies [entryPath] imports Map.empty
        { Units = deps; Main = start }