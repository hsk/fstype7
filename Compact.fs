module Compact
(*
 * Copyright (c) 2010-2013 h_sakurai, freecluster.net. All rights reserved.
 *
 * compact.fs
 * Functional Top Down Operator Precedence Compact eXPression parser
 *)

open System

type Pos(src:string, no:int) =
    member this.no = no
    member this.line:int =
        let rec getLineNo(start:int, line:int):int =
            let index = src.IndexOf('\n', start)
            if (index < 0) then 0
            else if (index >= no) then line
            else getLineNo(index+1, line + 1)
        getLineNo(0, 1)
    
    member this.src = src

    override this.ToString():string = this.p()
    
    member this.p():string =
        match this.line with
        | 0 -> "EOF"
        | n -> "(" + n.ToString() + ")"

let P0 = Pos("", 0)

exception SyntaxError of int * Pos * string

// 1000 - compact parser error
// 1001 lexer error '%s'
// 1002
// 1003 syntax error. expected is '%A' but found unexpected token %A\n%A 括弧の閉じタグが見つからなかった
// 1004 syntax error. expected is '%A' but found unexpected token %A\n%A %sに対応する開始の括弧が見つからなかった
// 1005 syntax error. expected is '%A' but found unexpected token %A\n%A %sに対応する開始の括弧が見つからなかった
// 1006 syntax error. expected is '%A' but found unexpected token %A\n%A %sの閉じ括弧が見つからなかった
// 1007 syntax error unexpected EOF
// 2000 - transduce error
// 2001 import parse error
// 2002 type parse error
// 2003 構造体のメンバのparse error
// 2004 関数のパラメータのparse error
// 2005 メインの変換のparse error

(** トークン *)
type Token =
    (** 識別子 *)
    | Id of Pos * string
    (** シンボル *)
    | Sym of Pos * string
    (** 倍精度浮動小数点数 *)
    | Dbl of Pos * double
    (** 64bit符号付き整数 *)
    | Lng of Pos * int64
    (** 文字列 *)
    | Str of Pos * string
    | Pre of Token * Token
    | Pst of Token * Token
    | Prn of Token * Token * Token
    | Bin of Token * Token * Token
    | Msg of Token * Token * Token * Token
    | St of Token * Token * Token * Token * Token
    | TNull of Pos

    override this.ToString() =
        match this with
        | Id(p,s) -> "Id(" + s + ")"
        | Sym(p,s) -> "Sym(" + s + ")"
        | Lng(p,i) -> "Lng(" + i.ToString() + ")"
        | Dbl(p,d) -> "Dbl(" + d.ToString() + ")"
        | Str(p,s) -> "Str(" + s + ")"
        | Pre(a,b) -> "Pre(" + a.ToString() + "," + b.ToString() + ")"
        | Pst(a,b) -> "Pst(" + a.ToString() + "," + b.ToString() + ")"
        | Prn(a,b,c) -> "Prn(" + a.ToString() + "," + b.ToString() + "," + c.ToString() + ")"
        | Bin(a,b,c) -> "Bin(" + a.ToString() + "," + b.ToString() + "," + c.ToString() + ")"
        | Msg(a,b,c,d) -> "Msg(" + a.ToString() + "," + b.ToString() + "," + c.ToString() + "," + d.ToString() + ")"
        | St(a,b,c,d,e) -> "St(" + a.ToString() + "," + b.ToString() + ")" + "," + c.ToString() + "," + d.ToString() + "," + e.ToString() + ")"
        | TNull p -> "TNull"
       
    member this.pos =
        match this with
        | Id(p,s) -> p
        | Sym(p,s) -> p
        | Lng(p,i) -> p
        | Dbl(p,d) -> p
        | Str(p,s) -> p
        | Pre(a,b) -> a.pos
        | Pst(a,b) -> a.pos
        | Prn(a,b,c) -> a.pos
        | Bin(a,b,c) -> a.pos
        | Msg(a,b,c,d) -> a.pos
        | St(a,b,c,d,e) -> a.pos
        | TNull p -> p

    member this.first =
        match this with
        | Id(p,s) -> this
        | Sym(p,s) -> this
        | Lng(p,i) -> this
        | Dbl(p,d) -> this
        | Str(p,s) -> this
        | Pre(a,b) -> a.first
        | Pst(a,b) -> a.first
        | Prn(a,b,c) -> a.first
        | Bin(a,b,c) -> a.first
        | Msg(a,b,c,d) -> a.first
        | St(a,b,c,d,e) -> a.first
        | TNull p -> this


(** 前置演算子の種類を表します。OpはOperator Prefixの略です。 *)
type Op =
    (** 左結合前置演算子 例) -1*)
    | Opl of int
    (** かっこ演算子 例) ( 1 ) *)
    | OpP of int * Token
    (** 文演算子 例) if ( true ) 3 *)
    | OpS of int * Token * Token

(** 演算子の種類を表します。OInはOperator Infixの略です。 *)
type OIn =
    (** 左結合２項演算子 *)
    | OIl of int
    (** 右結合２項演算子 *)
    | OIr of int
    (** メッセージ演算子 *)
    | OIp of int * Token
    (** 後置単項演算子 *)
    | OIe of int

(**
 * Compactパーサ
 * 
 * Compactは意味を持たないC言語のような式言語です。
 * compactオブジェクトを使う事でCompactをパースできます。
 * 
 * 下降型の演算子順位法を用いて構文解析します。
 *
 * usage:
 * {{{
 * let exp = compact("1+2*3")
 * println(exp)
 * }}}
 *)

open System.Text.RegularExpressions

module Parser =
    (** 前置演算子 *)
    let mutable prs =
        new Map<string, Op>(
                            [
                            "import", Opl(10);
                            "new", Opl(10);
                            "gcnew", Opl(10);
                            "sizeof", Opl(10);
                            "typedef", Opl(4);
                            "type", Opl(4);
                            "-", Opl(99);
                            "*", Opl(98);
                            "&", Opl(100);
                            "!", Opl(90);
                            "var", Opl(10);
                            "val", Opl(10);
                            "def", Opl(10);
                            "static", Opl(10);
                            "return", Opl(10);
                            "goto", Opl(10);
                            "case", OpP(31, Id(P0,":"));
                            "(", OpP(0, Id(P0,")"));
                            "{", OpP(0, Id(P0,"}"));
                            "[", OpP(0, Id(P0,"]"));

                            "cast", OpS(2, Id(P0,"("), Id(P0,")"));

                            "if", OpS(2, Id(P0,"("), Id(P0,")"));
                            "fun", OpS(2, Id(P0,"("), Id(P0,")"));
                            "mac", OpS(2, Id(P0,"("), Id(P0,")"));
                            "while", OpS(2, Id(P0,"("), Id(P0,")"));
                            "do", OpS(2, Id(P0,"{"), Id(P0,"}"));
                            "for", OpS(2, Id(P0,"("), Id(P0,")"))])
    (** 中置、後置、メッセージ演算子 *)
    let mutable ins =
        new Map<string, OIn>(
                            [
                            ".", OIl(100);
                            "->", OIl(100);
                            "=>", OIl(90);
                            ":", OIl(30);
                            "*", OIl(50);
                            "/", OIl(50);
                            "&", OIl(50);
                            "|", OIl(50);
                            "^", OIl(50);
                            "%", OIl(50);
                            "<<", OIl(50);
                            ">>", OIl(50);
                            ">>>", OIl(50);
                            "-", OIl(10);
                            "+", OIl(10);
                            "<", OIl(6);
                            "<=", OIl(6);
                            ">=", OIl(6);
                            ">", OIl(6);
                            "!=", OIl(5);
                            "==", OIl(5);
                            "&&", OIl(4);
                            "||", OIl(4);
                            ",", OIr(1);
                            "else", OIl(3);
                            "*=", OIr(5);
                            "/=", OIr(5);
                            "+=", OIr(5);
                            "-=", OIr(5);
                            "=", OIr(5);
                            "(", OIp(100, Id(P0,")"));
                            "{", OIp(100, Id(P0,"}"));
                            "[", OIp(100, Id(P0,"]"));

                            "++", OIe(5);
                            "--", OIe(5);
                            "?", OIe(4);
                            "is", OIl(3);
                            ";", OIe(3)
                            ])

    type LexV =
    | LCom
    | LCom1
    | LEol
    | LSym
    | LDNum
    | LXNum
    | LNum
    | LStr1
    | LPtn
    | LSpc1
    | LSpc
    | LEof

    let mms =
        [
            LCom,"""(/\*.*?\*/)""",1;
            LCom1,"""(//[^\r\n]*)(\r\n|\r|\n|)""",2;
            LEol,"""([;:])""",1;
            LSym,"""(')([^-\+*\/\(\)\[\]\{\}\s\=\;\:<>,\&\.%!]+)""",2;
            LDNum,"""([0-9]+\.[0-9]*)""",1;
            LXNum,"""(0x)([0-9A-Fa-f]+)(L?)""",3;
            LNum,"""([0-9]+)(L?)""",2;
            LStr1,"""("(\\.|[^"\\]*)*")""",2;
            LPtn,"""([-\+*\/\=<>&!]+|[\(\)\[\]\{\},\.%?]|[^-\+*\/\(\)\[\]\{\}\s\=\;\:<>,\&\.%!?]+|$)""",1;
            LSpc1,"""(\r\n|\r|\n)""",1;
            LSpc,"""([\s]+)""",1;
            LEof,"""((\r\n|\r|\n|\s)*$)""",2;
        ]
    let regex = Regex("^"+String.Join("|", List.map (function|(a,b,c)-> b) mms), RegexOptions.Singleline )
    
    let (_,ms1) = List.fold (fun (n,l) (a,b,c)->(c+n,(a,n,c+n-1)::l)) (1,[]) mms
    let ms = List.rev ms1
    let mutable connectf = true
    let mutable str = ""
    let mutable token: Token = TNull(P0)
    let mutable ptoken: Token = TNull(P0)
    let mutable offset = 0

    (**
     * パーサ
     * 
     * @param src: String パースしたい文字列
     *)
    let parse(src: string): Token =
        connectf <- true
        str <- src
        token <- TNull(P0)
        ptoken <- TNull(P0)
        offset <- 0
        let pos() = new Pos(src, offset)
    //    let pos() = new Pos(offset)
        let lex(): Token =
            ptoken <- token
            connectf <- true
            let rec t():unit =
                let setToken(s:int,t: Token):unit =
    //                t.pos = new Pos(src, offset)
                    offset <- offset + s
                    token <- t
                    str <- str.Substring(s)
            
                let reg str =
                    let m:Match = regex.Match(str)
                    if not m.Success then
                        None
                    else
                        let groups = [| for x in m.Groups -> x.Value |]
                        let rec getno (groups:string []) ms =
                            match ms with
                            | (sym,st:int,en)::ms ->
                                if (groups.[st] <> "") then
                                    let rec getlist i st (groups: string []) ls =
                                        if (i < st) then ls
                                        else getlist (i-1) st groups ((groups.[i])::ls)
                                    Some (sym, groups.[0]::(getlist en st groups []))
                                else
                                    getno groups ms
                            | [] -> Some(LEof,["";"";""])
                        getno groups ms

                let replaceStr(e:string):string =
                    //println("e='"+e+"'")
                    let e2 = e.Substring(1, e.Length - 2).
                                Replace("\\\"","\"").
                                Replace("\\b","\b").
                                Replace("\\f","\f").
                                Replace("\\n","\n").
                                Replace("\\r","\r").
                                Replace("\\t","\t").
                                Replace("\\\\","\\")
                    //    """\\u([0-9a-fA-F]{4})""".r.replaceAllIn(e2, m -> String.valueOf(Integer.parseInt(m.group(1), 16)) )
                    //println("e2='"+e2+"'")
                    e2
                match reg str with
                | Some(LCom,[o; a]) ->
                    str <- str.Substring(o.Length)
                    offset <- offset + o.Length
                    t()
                | Some(LCom1, [o; a; b]) ->
                    str <- str.Substring(o.Length)
                    offset <- offset + o.Length
                    t()
                | Some(LEol, [o; a]) ->
                    connectf <- false
                    setToken(o.Length,Id(pos(), a))
                | Some(LSym, [o; a; b]) -> setToken(o.Length,Sym(pos(), b))
                | Some(LDNum, [o; a]) -> setToken(o.Length,Dbl(pos(), Convert.ToDouble(a)))
                | Some(LXNum, [o; a; b; c]) -> setToken(o.Length,Lng(pos(), Convert.ToInt64(b,16)))
                | Some(LNum, [o; a; b]) -> setToken(o.Length,Lng(pos(), Convert.ToInt64(a)))
                | Some(LStr1, [o; a; b]) -> setToken(o.Length, Str(pos(), replaceStr(a)))
                | Some(LPtn, [o; a]) -> setToken(o.Length,Id(pos(), a))
                | Some(LSpc1, [o; a]) -> str <- str.Substring(o.Length); connectf <- false; offset<- offset + o.Length; t()
                | Some(LSpc, [o; a]) -> str <- str.Substring(o.Length); offset<- offset + o.Length; t()
                | Some(LEof, [o; a; b]) -> setToken(0,Id(pos(), ""))
                | _ -> raise(SyntaxError (1001, pos(), "lexer error '" + str + "'"))
            t()
            ptoken
        lex() |> ignore

        let eat(e: Token, er:Token, no:int, s:String): Token =
            match (lex(),e) with
            | (Id(_,a), Id(_,b)) when a = b -> ptoken
            | _ ->
                raise(SyntaxError(no,
                                  ptoken.pos,
                                  sprintf "syntax error. expected is '%A' but found unexpected token %A\n%A %s" e ptoken er.pos s))
        let rec exp(p: int): Token =
            let rec pr(t: Token): Token =
                match t with
                | Id(_, op) ->
                    //println("pr "+op)
                    match prs.TryFind(op) with
                    | Some(OpP(np, ep)) ->
                        let e = loop(exp(np),np)
                        let e2 = Prn(t, e, eat(ep,t,1003,"括弧の閉じタグが見つからなかった"))
                        //println("e2="+e2)
                        e2
                    | Some(Opl(np)) -> Pre(t, exp(np))
                    | Some(OpS(np, sp, ep)) ->
                        eat(sp, t, 1004, op+"に対応する開始の括弧が見つからなかった") |> ignore
                        let e = loop(exp(0), 0)
                        eat(ep, t, 1005, op+"に対応する終了の括弧が見つからなかった") |> ignore
                        St(t, sp, e, ep, exp(np))
                    | None -> t
                | _ -> t
            let rec inp(t: Token): Token =
                match token with
                | Id(_, op) ->
                    match ins.TryFind(op) with
                    | Some(OIl(np)) when (np > p) -> inp(Bin(t, lex(), exp(np)))
                    | Some(OIr(np)) when (np >= p) -> inp(Bin(t, lex(), exp(np)))
                    | Some(OIe(np)) when (np >= p) -> inp(Pst(t, lex()))
                    | Some(OIp(np, ep)) when (np > p && connectf) ->
                        let sp = lex()
                        let e = loop(exp(0), 0)
                        inp(Msg(t, sp, e, eat(ep,sp, 1006, op+"の閉じ括弧が見つからなかった")))
                    | _ -> t
                | _ -> t

            match token with
            | Id(_, ")") | Id(_, "}") | Id(_, "]") | Id(_, ":") -> Id(pos(), "void")
            | Id(_, "") -> raise(SyntaxError(1007, pos(), "syntax error unexpected EOF"))
            | _ ->
                let rc:Token = inp(pr(lex()))
//                Console.WriteLine (""+rc.ToString())
                rc

        and loop(t: Token, p:int): Token =
            match token with
            | Id(_, ")") | Id(_, "}") | Id(_, "]") | Id(_, ":") | Id(_,"") | Id(_,"void") -> t
            | _ ->
                let b = loop(exp(p), 0)
                Bin(t, Id(b.pos, "@"), b)
        loop(exp(0), 0)

let parse(src: string): Token = Parser.parse(src)

