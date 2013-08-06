module Main

open AST
open System

open System.Text.RegularExpressions

let mutable debug = true


type Opts = {
    files:string list;
    out:string;
    framework: string;
    link: bool;
    s: bool;
    run: bool;
    p: bool;
    llvm: bool;
    v: string;
    debug: bool;
    arch:string;
    bit:int
}

type Opts with
    // default values
    static member make() = {
        files = [];
        out = "";
        framework = "";
        link = true;
        s = false;
        run = false;
        p = false;
        llvm = false;
        v = "2";
        debug = false;
        arch = "x86-64";
        bit = 64
    }

(** 引数オプション *)
let mutable opt:Opts = Opts.make()

(**
 * LCCの追加オプション取得
 * 
 * @param arch:String アーキティクチャ x86 | x86-64
 * @return String 追加オプション文字列
 *)
let getLCCOption(arch:string):string =
    match opt.arch with
    | "x86" -> " -mattr=-avx"
    | "x86-64" -> " -mattr=-avx"
    | _ -> ""

let mutable tim = 0L

let benchStart () = 
    tim <- System.DateTime.Now.Ticks
(**
 * bench mark
 *)
let bench (str:string):unit =
    let t = System.DateTime.Now.Ticks
    let rc = (t - tim) / 10000L
    printfn "%s %d ms" str rc
    tim <- t
(**
 * コンパイル
 *)
let comp(sname:string, opt:Opts, src:string) =
    benchStart ()
    GlobalEnv.init()
    Env.init([])
    // パース
    let ast:Prog =
        match opt.p with
        | false ->
            let st = Compact.parse(src)
            bench "parse"
            if (debug) then
                printfn "st=%A" st
            Transduce.apply(st)
        | true -> raise(Exception("not support"))// parser.parse(src).get
    bench "transduce"

    if (debug) then
        printfn "ast=%A" ast

    // 型付け
    let ast2 = Alpha.apply(ast)
    bench "alpha"
    let tast = Typing.apply(ast2)
    bench "typing"
    if (debug) then
        printfn "tast=%A" tast
    
    let lname = Regex(".s$").Replace(sname, ".ll")

    let llcodes = KNormal.apply(tast)
    bench "k normal"
    let llcodes2 = ConstFold.apply(llcodes)
    bench "const fold"
    LLEmit.apply(lname, llcodes2)
    bench "emit"
    let opt1 = getLCCOption(opt.arch)
    let cmd = "llc -march="+opt.arch+" "+lname+ " -o " + sname + opt1
    if (debug) then
        Console.WriteLine cmd

    match Exec.run(cmd) with 
    | (0, _, _) -> ()
    | (_, output, error) ->
        Console.WriteLine output
        raise(Exception(error))

    // アセンブル
    if not opt.s then
        let oname = Regex(".s$").Replace(sname, ".o")
        let cmd = sprintf "gcc -c -m%d %s -o %s" opt.bit sname oname 
        if (debug) then
            Console.WriteLine cmd
        match Exec.run(cmd) with
        | (0,_,_) -> ()
        | (_,output,error) ->
            Console.WriteLine(output)
            raise(Exception(error))

(**
 * アーキティクチャを標準化する
 * 
 * @param arch:String アーキティクチャ x86 | x86-64 | i386
 * @return Int ビット数 32 | 64
 *)
let getArch(arch: string):string =
    match arch with
    | "i386" -> "x86"
    | "amd64" -> "x86-64"
    | arch -> arch


(**
 * アーキティクチャごとのビット数取得
 * 
 * @param arch:String アーキティクチャ x86 | x86-64
 * @return Int ビット数 32 | 64
 *)
let getArchBit(arch: string):int =
    match arch with
    | "x86" -> 32
    | "x86-64" -> 64
    | _ ->
        raise(Exception("error "+arch+" is unsupport arch."))

(**
 * オプションパース＆値設定処理
 * 
 * 末尾再帰最適化されたステートマシンとして実装してあります
 *)
let rec opts(args:string list, m:Opts) :Opts =
    match args with
    | "-c"::xs -> opts(xs,  {m with link = false})
    | "-S"::xs -> opts(xs, {m with link = false; s = false})
    | "-run"::xs -> opts(xs, {m with run = true})
    | "-d"::xs -> opts(xs, {m with debug = true})
    | "-o"::o::xs -> opts(xs, {m with out = o})
    | "-p"::xs -> opts(xs, {m with p = true})
    | "-llvm"::xs -> opts(xs, {m with llvm = true})
    | "-v"::v::xs -> opts(xs, {m with v = v})
    | "-framework"::f::xs -> opts(xs, {m with framework = m.framework + " -framework "+f})
    | "-march"::arch::xs -> opts(xs, {m with arch=getArch(arch); bit= getArchBit(getArch(arch))})
    | n::xs -> opts(xs, {m with files = n::m.files})
    | [] -> m

(**
 * test main
 *)
let test_main(args: string []):int =
    try
        benchStart()
        Test.test("test/test_global_var/test_0005.lll")
        // Test.test("test/test_global_var/test_0004.lll")
        //        Test.test("test/test_byte/test_0006.lll")
        //Test.test("sample/hello.lll")
        Test.tests()
        bench "end"
        0
    with
    | e ->
        printfn "%A" e
        1
    
(**
 * シンプルなメイン関数
 *)
let main1 (args: string []):int =
    try
        GlobalEnv.init()
        Env.init([])

        let prg = Exec.readAll(args.[0])
        let st = Compact.Parser.parse(prg)
        let ast = Transduce.apply(st)
        let ast2 = Alpha.apply(ast)
        let tast = Typing.apply(ast2)
        let llcodes = KNormal.apply(tast)
        let llcodes2 = ConstFold.apply(llcodes)
        LLEmit.apply("e.ll", llcodes2)
        Exec.run("llc -march=x86-64 e.ll -o e.s") |> ignore
        Exec.run("gcc -m64 e.s lib/gc.c lib/stdio.c") |> ignore
        0
    with
        | e ->
            printfn "%A" e
            1

open Compact
open Typing

(**
 * 本格的なメイン関数
 *)
let main2 (args:string []):int =

    try
        let args1 = List.ofArray(args)
        let os = System.Environment.OSVersion
        let opt =
            match os.Platform with
            | System.PlatformID.Win32Windows
            | System.PlatformID.Win32NT
            | System.PlatformID.Win32S
            | System.PlatformID.WinCE ->
                opts("-march"::"x86"::args1, Opts.make())
            | System.PlatformID.Unix ->
                opts("-march"::"amd64"::args1, Opts.make())
            | System.PlatformID.Xbox ->
                opts("-march"::"xbox"::args1, Opts.make())
            | System.PlatformID.MacOSX ->
                opts("-march"::"mac"::args1, Opts.make())
            | _ -> raise(Exception "unsupport envirionment")

        debug <- opt.debug

        match opt.files with
        | [] ->
            raise(Exception("usage: dtype [-c][-run][-d][-o filename][-march x86|x86-64] filenames..."))
        | _ ->
            let f1 fs name =
                if not(Regex(".*\\.lll$").IsMatch(name)) then
                    raise(Exception("error! file extension need .lll, but filename is " + name))
                if (debug) then
                    Console.WriteLine("file " + name)
                let sname = Regex(".lll$").Replace(name, ".s")
                let oname = Regex(".lll$").Replace(name, ".o")
                let src = Exec.readAll(name)
                imports <- name :: imports
                Env.filename <- name
                comp(sname, opt, src)
                oname::fs
                                
            let objs = List.rev(List.fold f1 [] opt.files)

            if opt.link then
                let out2 = if (opt.out = "") then (List.head objs) else opt.out
                let out3 = Regex("(\\.lll|\\.o)$").Replace(out2, "")
                let cmd = 
                    "gcc -m" + opt.bit.ToString() + " -o " + out3 + " " + 
                    (List.fold (fun file cmd -> cmd + " " + file) "" objs) +
                    " lib/gc.c lib/stdio.c " + opt.framework

                if (debug) then
                    Console.WriteLine(cmd)
                
                match (Exec.run cmd) with
                | (0, _, _) ->
                    if (opt.run) then
                        let (code, output, err) = Exec.run("./" + out3)
                        Console.WriteLine(output)
                        code
                    else 0

                | (code, output, error) ->
                    Console.Write output
                    Console.Write error
                    code
            else 0                    
    with
    | e ->
        printfn "%A" e
        1


[<EntryPoint>]
let main(args:string []):int =
    test_main args
    // main1 args
    // main2 args
    //main2 ("sample/opengl.lll sample/program.lll -run -framework OpenGL -framework glut".Split(' '))
    //main2 ("sample/opengl.lll sample/shoot.lll -run -framework OpenGL -framework glut".Split(' '))
