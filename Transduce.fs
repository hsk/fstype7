(**
 * トランデューサ
 *)

module Transduce

open AST
open System
open Compact

type Token with
    member this.p =
        new AST.P(this.pos.src, this.pos.no)

(**
 * 多値内の１個目のトークンを取得
 * 
 * @param a: Any
 * @return Token
 *)
let rec findToken(a: Token): Token = a.first

(**
 * 複数の式の変換
 *)
let rec fimport(st: Token): String =
    match st with
    | Bin(Id(_, a), Id(_, "."), b) -> a + "/" + fimport(b)
    | Id(_, a) -> a
    | o -> raise(SyntaxError(o.pos, "error syntax error " + o.first.ToString() + " " + o.ToString()))

(**
 * 型の変換
 *)
let rec t(st: Token): T =
    match st with
    | Msg(Id(_, "Ptr"), Id(_, "["), a, Id(_, "]")) -> Tp(t(a))
    | Msg(Id(_, "Array"), Id(_, "["), Bin(a, Id(_, ","), Lng(_, b)), Id(_, "]")) -> TArr(t(a), b)
    | Bin(a, Id(_, "=>"), b) -> TFun(t(b), ts(a))
    | Msg(a, Id(_, "["), Lng(_, b), Id(_, "]")) -> TArr(t(a), b)
    | Id(_, "byte") -> Ti(8)
    | Id(_, "short") -> Ti(16)
    | Id(_, "int") -> Ti(32)
    | Id(_, "long") -> Ti(64)
    | Id(_, "float") -> Tf
    | Id(_, "double") -> Td
    | Id(_, "void") -> Tv
    | Pre(Id(_, "*"), a) -> Tp(t(a))
    | Msg(Id(_, "struct"), Id(_, "{"), b, Id(_, "}")) -> TStr(members(b, []))
    | Prn(Id(_, "("), a, Id(_, ")")) -> t(a)
    | Id(_, s) -> TDef(s)
    | o ->
        raise(SyntaxError(o.pos, "error syntax error " + o.first.ToString() + " " + o.ToString()))

(**
 * 型リストの変換
 *)
and ts(st: Token): T list =
    //println("members "+st)
    match st with
    | Prn(Id(_, "("), a, Id(_, ")")) ->
        ts(a)
    | Bin(a, Id(_, ","), b) ->
        t(a) :: ts(b)
    | a ->
        match t(a) with
        | Tv -> []
        | t -> [t]
(**
 * 構造体のメンバの変換
 *)
and members(st: Token, m: (string * T) list): (string * T) list =
    //println("members "+st)
    match st with
    | Id(_, "void") -> m
    | Bin(Id(_, a), Id(_, ":"), b) -> (a, t(b)) :: m
    | Pst(a, Id(_, ";")) -> members(a, m)
    | Bin(a, Id(_, "@"), b) -> members(a, members(b, m))
    | o -> raise(SyntaxError(o.pos, "error syntax error " + o.first.ToString() + " " + o.ToString()))

(**
 * 関数のパラメータの変換
 *)
let fprms(st: Token): (string * T) list =
    let rec ff(st: Token, m: (string * T) list): (string * T) list =
        match st with
        | Bin(a, Id(_, ","), b) -> ff(b, ff(a, m))
        | Bin(Id(_, a), Id(_, ":"), typ) -> (a, t(typ)) :: m
        | Id(_, "void") -> m
        | o -> raise(SyntaxError(o.pos, "error syntax error " + o.first.ToString() + " " + o.ToString()))
    List.rev (ff(st, []))

(**
 * メインの変換関数
 * 
 * @param st: Any 変換元のcompactデータ
 * @return E 式
 *)
let rec f(o: Token): E =
    // println("f "+st)
    match o with
    | Pre(Id(_, "import"), f) ->
        EImport(o.p, fimport(f))
    | Bin(Pre(Id(_, "def"), Bin(Msg(Id(_, name), Id(_, "("), r, Id(_, ")")), Id(_, ":"), typ)), Id(_, "="), b) ->
        EFun(o.p, t(typ), name, fprms(r), f(b))
    | Pre(Id(_, "def"), Msg(Msg(Id(_, name), Id(_, "("), r, Id(_, ")")), (Id(_, "{") as o2), e, Id(_, "}"))) ->
        EFun(o.p, Tv, "" + name, fprms(r), EBlock(o2.p, Tn, fs(e)))
    | Pre(Id(_, "def"), Bin(Msg(Id(_, name), Id(_, "("), b, Id(_, ")")), Id(_, ":"), typ)) ->
        GlobalEnv.add(name, TFun(t(typ), List.map (fun (id, t) -> t) (fprms b)))
        ENop(o.p, Tv, "def function")
    | Prn(Id(_, "{"), e, Id(_, "}")) -> EBlock(o.p, Tn, fs(e))
    | Lng(_, a) -> ELd(o.p, Tn, a)
    | Dbl(_, a) -> ELdd(o.p, Tn, a)
    | Str(_, a) -> ELds(o.p, Tn, a)
    | Pre(Id(_, "-"), Lng(_, a)) -> ELd(o.p, Ti(64), -a)
    //            | (o@Id(_, "-"), Dbl(a)) -> p(o,ELdd(Td, -a)) 
    | Bin(Pre(Id(_, "var"), Bin(Id(_, a), Id(_, ":"), t1)), Id(_, "="), b) -> EVar(o.p, t(t1), a, f(b))
    | Bin(Pre(Id(_, "var"), Id(_, a)), Id(_, "="), b) -> EVar(o.p, Tn, a, f(b))
    | Bin(Pre(Id(_, "val"), Bin(Id(_, a), Id(_, ":"), t1)), Id(_, "="), b) -> EVal(o.p, t(t1), a, f(b))
    | Bin(Pre(Id(_, "val"), Id(_, a)), Id(_, "="), b) -> EVal(o.p, Tn, a, f(b))
    | Bin(a, Id(_, "="), b) -> binf(EAssign, a, b)
    | Msg(a, Id(_, "["), b, Id(_, "]")) -> binf(EArray, a, b)
    | Pre(Id(_, "*"), a) -> EPtr(o.p, Tn, f(a))
    | Pre(Id(_, "&"), a) -> ERef(o.p, Tn, f(a))
    | Pre(Id(_, "new"), Msg(a, Id(_, "["), b, Id(_, "]"))) -> ENewArray(o.p, Tp(t(a)), f(b))
    | Pre(Id(_, "sizeof"), a) ->
        try
            let t1 = t(a)
            ESizeOf(o.p, Ti(64), t1, ENull(o.p))
        with
        | _ -> ESizeOf(o.p, Ti(64), Tn, f(a))
        
    | Id(_, "return") -> ERet(o.p, Tn, ENop(o.p, Tv, "void"))
    | Pre(Id(_, "return"), Id(_, ";")) -> ERet(o.p, Tv, ENop(o.p, Tv, "void"))
    | Pre(Id(_, "return"), a) -> ERet(o.p, Tn, f(a))
    | Pre(Id(_, "new"), a) -> ENew(o.p, Tp(t(a)))
    | Pre(Id(_, "gcnew"), a) -> EGCNew(o.p, Tp(t(a)))
    | St(Id(_, "cast"), Id(_, "("), t1, Id(_, ")"), a) -> ECast(o.p, t(t1), f(a))
    | Bin(a, Id(_, "+"), b) -> bin("add", a, b)
    | Bin(a, Id(_, "-"), b) -> bin("sub", a, b)
    | Bin(a, Id(_, "*"), b) -> bin("mul", a, b)
    | Bin(a, Id(_, "/"), b) -> bin("div", a, b)
    | Bin(a, Id(_, "%"), b) -> bin("mod", a, b)
    | Pre(Id(_, "-"), a) -> ENeg(o.p, Tn, f(a))
    | Bin(a, Id(_, "<<"), b) -> bin("shl", a, b)
    | Bin(a, Id(_, ">>>"), b) -> bin("shr", a, b)
    | Bin(a, Id(_, ">>"), b) -> bin("ushr", a, b)
    | Bin(a, Id(_, "&"), b) -> bin("and", a, b)
    | Bin(a, Id(_, "|"), b) -> bin("or", a, b)
    | Bin(a, Id(_, "^"), b) -> bin("xor", a, b)
    | Bin(a, Id(_, "&&"), b) -> bin("and", a, b)
    | Bin(a, Id(_, "||"), b) -> bin("or", a, b)
    | Pre(Id(_, "!"), a) -> ENot(o.p, Tn, f(a))
    | Bin(a, Id(_, "<="), b) -> bin("le", a, b)
    | Bin(a, Id(_, "<"), b) -> bin("lt", a, b)
    | Bin(a, Id(_, ">="), b) -> bin("ge", a, b)
    | Bin(a, Id(_, ">"), b) -> bin("gt", a, b)
    | Bin(a, Id(_, "=="), b) -> bin("eq", a, b)
    | Bin(a, Id(_, "!="), b) -> bin("ne", a, b)
    | Bin(a, (Id(_, "+=") as o), b) -> f(Bin(a, Id(o.pos, "="), Bin(a, Id(o.pos, "+"), b)))
    | Bin(a, (Id(_, "-=") as o), b) -> f(Bin(a, Id(o.pos, "="), Bin(a, Id(o.pos, "-"), b)))
    | Pst(a, (Id(_, "++") as o)) -> f(Bin(a, Id(o.pos, "="), Bin(a, Id(o.pos, "+"), Lng(o.pos, 1L))))
    | Pst(a, (Id(_, "--") as o)) -> f(Bin(a, Id(o.pos, "="), Bin(a, Id(o.pos, "-"), Lng(o.pos, 1L))))
    | Pst(a, Id(_, ";")) -> f(a)
    | Pre(Id(_, "var"), Bin(Id(_, a), Id(_, ":"), b)) -> EVar(o.p, t(b), a, ENull(o.p))
    | Pre(Id(_, "typedef"), Bin(Id(_, a), Id(_, "="), b)) -> ETypeDef(o.p, t(b), a)
    | Id(_, "void") -> ENop(o.p, Tv, "void")
    | Id(_, "break") -> EBreak(o.p, Tn)
    | Id(_, "continue") -> EContinue(o.p, Tn)
    | Id(_, a) -> EId(o.p, Tn, a)
    | Msg(a, Id(_, "("), b, Id(_, ")")) ->
        let o = f(a)
        ECall(o.pos, Tn, o, prms(b))
    | Bin(a, Id(_, "."), Id(_, b)) ->
        let o = f(a)
        EField(o.pos, Tn, Tn, o, b)
    | Bin(a, Id(_, "->"), Id(_, b)) ->
        let o = f(a)
        EArrow(o.pos, Tn, Tn, o, b)
    | St(Id(_, "if"), Id(_, "("), a, Id(_, ")"), Bin(b, Id(_, "else"), c)) ->
        EIf(o.p, Tn, f(a), f(b), f(c))
    | St(Id(_, "if"), Id(_, "("), a, Id(_, ")"), b) ->
        EIf(o.p, Tn, f(a), f(b), ENop(o.p, Tv, "void"))
    | St(Id(_, "while"), Id(_, "("), a, Id(_, ")"), b) -> EWhile(o.p, Tn, f(a), f(b))
    | St(Id(_, "for"), Id(_, "("), Pst(Id(_, ";"), Id(_, ";")), Id(_, ")"), b) ->
        EFor(o.p, Tn, ENop(o.p, Tn, ""), ENop(o.p, Tn, ""), ENop(o.p, Tn, ""), f(b))
    | St(Id(_, "for"), Id(_, "("), Bin(a, Id(_, "@"), Pst(b, Id(_, ";"))), Id(_, ")"), body) ->
        EFor(o.p, Tn, f(a), f(b), ENop(body.p, Tn, ""), f(body))
    | St(Id(_, "for"), Id(_, "("), Bin(a, Id(_, "@"), Bin(b, Id(_, "@"), c)), Id(_, ")"), body) ->
        EFor(o.p, Tn, f(a), f(b), f(c), f(body))
    | Bin(a, Id(_, "is"), Prn(Id(_, "{"), b, Id(_, "}"))) -> ESwitch(o.p, Tn, f(a), switches(b))
    | Pst(Id(_, "_"), Id(_, "?")) -> ECase(o.p, Tn, ENull(o.p), ENop(o.p, Tv, ""))
    | Pst(a, Id(_, "?")) -> ECase(o.p, Tn, f(a), ENop(o.p, Tv, ""))
    | Msg(Msg(Id(_, "switch"), Id(_, "("), a, Id(_, ")")), Id(_, "{"), b, Id(_, "}")) ->
        ESwitch(o.p, Tn, f(a), switches(b))
    | St(Id(_, "do"), Id(_, "{"), a, Id(_, "}"), St(Id(_, "while"), Id(_, "("), b, Id(_, ")"), Id(_, ";"))) ->
        EDo(o.p, Tn, fs(a), f(b))
    | Pre(Id(_, "goto"), Id(_, a)) -> EGoto(o.p, Tn, a)
    | Prn(Id(_, "("), (Bin(_, Id(_, ","), _) as a), Id(_, ")")) -> ETuple(o.p, Tn, tpl(a))
    | Prn(Id(_, "("), a, Id(_, ")")) -> f(a)
    | Bin(Id(_, "default"), Id(_, ":"), b) -> ECase(o.p, Tn, ENull(o.p), f(b))
    | Bin(Id(_, a), Id(_, ":"), b) -> ELabel(o.p, Tn, a, f(b))

    | Pre(Id(_, "case"), Bin(a, Id(_, ":"), b)) -> ECase(o.p, Tn, f(a), f(b))
    | Prn(Id(_, "case"), Id(_, "_"), Id(_, ":")) -> ECase(o.p, Tn, ENull(o.p), ENop(o.p, Tv, ""))
    | Prn(Id(_, "case"), a, Id(_, ":")) -> ECase(o.p, Tn, f(a), ENop(a.p, Tv, ""))
    | o -> raise(SyntaxError(o.first.pos, "error syntax error " + o.first.ToString() + " " + o.ToString()))

(**
 * ２項の構文木を作成し、１つ目の項の位置にする
 *)
and binf(f1: (P * T * E * E) -> E, a: Token, b: Token): E =
    let a1 = f(a)
    let a2 = f(b)
    let e = f1(a1.pos, Tn, a1, a2)
    //e.pos = a1.pos
    e

(**
 * 2項演算子
 * 
 * @param f1: String 演算子名
 * @param a: Any 左の構文木
 * @param b: Any 右の構文木
 * @return E 式
 *)
and bin(op: string, a: Token, b: Token): E =
    let (a1, a2) = (f(a), f(b))
    let e = EBin(a1.pos, Tn, Tn, op, a1, a2)
    //e.pos = a1.pos
    e

(**
 * 多値(タプル)の変換
 *)
and tpl(a: Token): E list =
    match a with
    | Bin(a, Id(_, ","), b) -> tpl(a) @ tpl(b)
    | o -> [f(o)]

(**
 * 複数の式の変換
 *)
and fs(st: Token): E list =
    match st with
    | Bin(a, Id(_, "@"), b) -> fs(a) @ fs(b)
    | a -> [f(a)]

(**
 * スイッチ内のケースの操作
 *)
and switches(e: Token): (E * E) list =
    let rec f(l: E list, r: (E * E) list, casee: E, casel: E list): (E * E) list =
        match l with
        | [] ->
            let r2 =
                match casee with
                | ENull(_) -> r
                | _ ->
                    let ls = List.rev casel
                    let head =
                        match ls with
                        | [] -> casee
                        | a::_ -> a
                    (casee, EBlock(head.pos, Tn, ls)) :: r
            List.rev r2
        | (ECase(p, t, a, b) as e) :: l ->
            let r2 =
                match casee with
                | ENull(_) -> r
                | _ ->
                    let ls = List.rev casel
                    let head =
                        match ls with
                        | [] -> casee
                        | a::_ -> a
                    (casee, EBlock(head.pos, Tn, ls)) :: r
            f(l, r2, e, [b])
        | e :: l -> f(l, r, casee, e :: casel)
    f(fs(e), [], ENull(e.p), [])

(**
 * 関数パラメータ等の変換
 *)
and prms(st: Token): E list =
    match st with
    | Bin(a, Id(_, ","), b) -> f(a) :: prms(b)
    | a -> [f(a)]

let apply(st: Token): Prog =
    Prog(fs(st))

