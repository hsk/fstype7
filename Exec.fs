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
