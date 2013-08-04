module Asm

open System.IO
open System.Text

let mutable writer:StreamWriter = null

let openFile(file:string): unit =
    writer <- new StreamWriter(file, false, new UTF8Encoding())

let p(str:string):unit =
    writer.WriteLine(str)

let p__(str:string):unit =
    writer.WriteLine("        "+str)

let close() =
    writer.Close()
