module Exec

open System.IO
open System.Text
open System.Diagnostics
open System.Text.RegularExpressions

let readAll(filename:string):string =
    File.ReadAllText(filename, Encoding.UTF8)

let run (cmd:string):(int * string * string) =
    let mutable args = Regex.Split(cmd, "[ \t]+", RegexOptions.IgnoreCase)
    let program = args.[0]
    let proc = new Process()
    proc.StartInfo <- new ProcessStartInfo()
    proc.StartInfo.FileName <- program
    proc.StartInfo.Arguments <- System.String.Join(" ", Array.sub args 1 (args.Length-1) )
    proc.StartInfo.UseShellExecute <- false
    proc.StartInfo.RedirectStandardOutput <- true
    proc.StartInfo.RedirectStandardError  <- true
    proc.Start() |> ignore
    proc.WaitForExit()
    (proc.ExitCode, proc.StandardOutput.ReadToEnd() ,proc.StandardError.ReadToEnd())

let compile(file:string) =
    try
        GlobalEnv.init()
        Env.init([])
        
        printfn "compile %s" file
        let src = readAll(file)
//        printfn "src = %s" src
        let st = Compact.Parser.parse(src)
        let ast = Transduce.apply(st)
        let ast2 = Typing.apply(ast)
        printfn "ast2 = %A" ast2
        let codes = KNormal.apply(ast2)
        let codes2 = ConstFold.apply(codes)
        printfn "%A" codes2
        LLEmit.apply("e.s", codes2)
        printfn "%A" (run "llc e.s")
        printfn "%A" (run "llvm-gcc -m64 e.s.s -o e lib/stdio.c")
    with
        e ->
            printfn "%s" e.StackTrace
            raise e
            