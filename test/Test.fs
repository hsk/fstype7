module Test

open System
open System.Text.RegularExpressions

let compile(file:string) =
    try
        GlobalEnv.init()
        Env.init([])
        
        printfn "compile %s" file
        let src = Exec.readAll(file)
//        printfn "src = %s" src
        let st = Compact.Parser.parse(src)
        let ast = Transduce.apply(st)
        let ast2 = Typing.apply(ast)
        printfn "ast2 = %A" ast2
        let codes = KNormal.apply(ast2)
        let codes2 = ConstFold.apply(codes)
        printfn "%A" codes2
        LLEmit.apply("e.s", codes2)
        printfn "%A" (Exec.run "llc e.s")
        printfn "%A" (Exec.run "llvm-gcc -m64 e.s.s -o e lib/stdio.c")
    with
        e ->
            printfn "%s" e.StackTrace
            raise e

let rec dirsUnder (path : string) = 
    [
        let sFiles = System.IO.Directory.GetFiles(path)
        yield! sFiles
        let sDirs = System.IO.Directory.GetDirectories (path) 
        for subDir in sDirs do 
            yield! dirsUnder subDir 
     ] 

let test file =
    printfn "test %s" file
    let src = Exec.readAll(file)
    if Regex("^///>>skip").IsMatch(src)
    then
        ()
    else
        
        let name = (Regex("///>(.*)").Match(src).Groups.Item 1).Value
        let expected1 = (Regex("""/\*\*\* result.*?(\(.*?\)).*?result \*\*\*/""", RegexOptions.Singleline).Match(src).Groups.Item 1).Value
        let expected = expected1.Replace("\r\n","\n").Replace("\r","\n")
            
        printfn "%s" name
        
        try
            GlobalEnv.init()
            Env.init([])
            
            let st = Compact.Parser.parse(src)
            let ast = Transduce.apply(st)
            let ast1 = Alpha.apply(ast)
            let ast2 = Typing.apply(ast1)
            printfn "ast2 = %A" ast2
            let codes = KNormal.apply(ast2)
            let codes2 = ConstFold.apply(codes)
            printfn "%A" codes2
            LLEmit.apply("e.s", codes2)
            let cmp = (Exec.run "llc -mcpu=x86-64 e.s")
            match cmp with
            | (0,_,_) -> printfn "%A" cmp
            | _ -> raise (Exception(sprintf "%A" cmp))
            
            let link = (Exec.run "llvm-gcc -m64 e.s.s -o e lib/stdio.c")
            match link with
            | (0,_,_) -> printfn "%A" link
            | _ -> raise (Exception(sprintf "%A" link))
            let result =
                match (Exec.run "./e") with
                | (a,b,c) -> "("+a.ToString()+","+b.Replace("\r\n","\n").Replace("\r","\n")+","+c.Replace("\r\n","\n").Replace("\r","\n")+")"
            if result = expected then
                Console.WriteLine(file + " ok")
            else
                raise(Exception(sprintf "error test %s %s\nexpected = %s but result = %s" file name expected result)    )
        with
            | AST.TypeError(no,p,m) as e ->
                printfn "%d %s '%s'" p.no m expected
                if expected = "(null)" then ()
                else if expected = "("+no.ToString()+")" then ()
                else raise e
            | e ->
                printfn "%s" e.StackTrace
                if expected = "(null)" then () else raise e
            
let tests() =
    let f (n:int) (src:string) =
        test src
        n + 1
    let no = List.fold f 0 (dirsUnder ("test")) 
    printfn "%d test ok" no
