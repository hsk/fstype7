(**
 * LLVMコードジェネレータ
 *)
module LLEmit

open System
open AST
open System.Text.RegularExpressions

type Const =
    | CStr of string * string * T
    | CNum of string * int * T
    
(**
 * 定数リスト
 *)
let mutable consts:Const list = []
  
(**
 * `=` 付きの出力をします。
 * 
 * rがnullかどうかチェックしてnullだった場合は`=`なしで出力し、nullでなければ`=`ありで出力します。
 *)
let p(id: R, out: string):unit =
    if (id <> RNULL)
    then Asm.p__(id.p + " = " + out)
    else Asm.p__(out)

(** 出力完了関数リスト *)
let mutable completeds:string list = []

let comment(out:string) :unit =
    Asm.p__("; " + (Regex("\\n").Replace(out,"\n        ; ")))
    
(**
 * LL出力
 * 
 * 引数lをファイルに出力します。
 *)
let rec output(l: LL):unit =
    match l with
    | LLCall(id, op, prms) ->

        let r =
            match op with
            | RL(Tp(t), _) ->
                let r = KNormal.genRL(t)
                p(r, "load " + Tp(t).p + " " + op.p)
                r
            | _ -> op

        let ps = String.Join(", ", List.map (fun (a:R) -> a.t.p + " " + a.p ) prms)

        match id.t with
        | Tv -> Asm.p("call " + id.t.p2 + " " + r.p + "(" + ps + ") nounwind ssp")
        | _ -> p(id, "call " + id.t.p2 + " " + r.p + "(" + ps + ") nounwind ssp")

    | LLUnary(id, op, a) ->

        match (a.t, op) with
        | (Ti _, "not") ->
            let r = KNormal.genRL(Ti(1))
            p(r, "icmp eq " + a.t.p + " 0, " + " " + a.p)
            p(id, "zext i1 " + r.p + " to " + id.t.p)
        | (Ti _, "neg") -> p(id, "sub " + a.t.p + " 0, " + a.p)
        | (Tf, "neg") | (Td, "neg") -> p(id, "fsub " + a.t.p + " 0.0, " + a.p)
        | _ -> raise(TypeError(5001,P0,sprintf "error %A" l))

    | LLBin(r, op, a, b) ->
        match (a.t, op) with

        | (Tp(t), "add") ->
            // TODO: 型推論の際にcastを入れなくする
            let id2 = GenId.genid("%..")
            Asm.p(id2 + " = ptrtoint " + b.t.p + " " + b.p + " to " + Ti(64).p)
            p(r, "getelementptr inbounds " + a.t.p + " " + a.p + ", " + Ti(64).p + " " + id2)

        | (Tp(t), "sub") ->
            // TODO: 型推論の際にcastを入れなくする
            let id2 = GenId.genid("%..")
            let id3 = GenId.genid("%..")
            Asm.p(id2 + " = ptrtoint " + b.t.p + " " + b.p + " to " + Ti(64).p)
            Asm.p(id3 + " = sub " + Ti(64).p + " 0, " + id2)
            p(r, "getelementptr inbounds " + a.t.p + " " + a.p + ", " + Ti(64).p + " " + id3)

        | (Tf, _) | (Td, _) ->
            match op with
            | "lt" | "le" | "gt" | "ge" | "eq" | "ne" ->
                let r2 = KNormal.genRL(Ti(1))
                p(r2, "fcmp o" + op + " " + a.t.p + " " + a.p + ", " + b.p)
                p(r, "zext i1 " + r2.p + " to i64")
            | _ ->
                p(r, "f" + op + " " + r.t.p + " " + a.p + ", " + b.p)
        | (Ti(_), "div") -> p(r, "sdiv " + r.t.p + " " + a.p + ", " + b.p)
        | (Ti(_), "mod") -> p(r, "srem " + r.t.p + " " + a.p + ", " + b.p)
        | (Ti(_), "shr") -> p(r, "ashr " + r.t.p + " " + a.p + ", " + b.p)
        | (Ti(_), "ushr") -> p(r, "lshr " + r.t.p + " " + a.p + ", " + b.p)
        | _ ->
            match op with
            | "eq" | "ne" ->
                let r2 = KNormal.genRL(Ti(1))
                p(r2, "icmp " + op + " " + a.t.p + " " + a.p + ", " + b.p)
                p(r, "zext i1 " + r2.p + " to i64")
            | "lt" | "le" | "gt" | "ge" ->
                let r2 = KNormal.genRL(Ti(1))
                p(r2, "icmp s" + op + " " + a.t.p + " " + a.p + ", " + b.p)
                p(r, "zext i1 " + r2.p + " to i64")
            | _ ->
                p(r, op + " " + r.t.p + " " + a.p + ", " + b.p)

    | LLLoad(r: R, s: R) ->
        p(r, "load " + s.t.p + " " + s.p)

    | LLStore(s: R, r: R) ->
        Asm.p__("store " + s.t.p + " " + s.p + ", " + r.t.p + " " + r.p)

    | LLAlloca(r: R) ->
        comment(r.ToString())
        p(r, "alloca " + r.t.p)

    | LLField(r: R, addr: R, RNULL, a: R) ->
        p(r, "getelementptr inbounds " + addr.t.p + " " + addr.p + ", " + a.t.p + " " + a.p)

    | LLField(r: R, addr: R, zero: R, a: R) ->
        match addr.t.stripType(P0, []) with
        | Tp((TArr _ | TStr _ | TCls _) as tt) ->
            p(r, "getelementptr inbounds " + addr.t.p + " " + addr.p + ", " + zero.t.p + " " + zero.p + ", " + a.t.p + " " + a.p)
        | _ ->
            p(r, "getelementptr inbounds " + addr.t.p + " " + addr.p + ", " + a.t.p + " " + a.p)

    | LLFun(t, n, ps, m, ls, r) ->
        consts <- []
        completeds <- n :: completeds
        Asm.p("define " + t.p + " @" + n + "(" + String.Join(", ", List.map (fun (a, t:T) -> t.p + " %" + a + ".v" ) ps) + ") nounwind ssp {")
        Asm.p("entry:")
        List.iter output ls

        match (t.stripType(P0, []), r) with
        | (_, RNULL) | (Tv, _) -> Asm.p__("ret " + t.p)
        | _ ->
            Asm.p__("store " + t.p + " " + r.p + ", " + Tp(t).p + " %..retVal")
            Asm.p__("br label %..leave")
            Asm.p("..leave:")
            let r2 = KNormal.genRL(t)
            p(r2, "load " + Tp(t).p + " %..retVal")
            Asm.p__("ret " + t.p + " " + r2.p)
        Asm.p("}")
        List.iter (fun (a:Const) ->
            match a with
            | CStr(id, asc, t) ->
                let a2 = asc.Replace("\\","\\\\")
                let a3 = a2.Replace("\"", "\\" + (sprintf "%x" (int '"')))
                Asm.p("@." + id + "= private constant " + t.p + " c\"" + a3 + "\\00\"")
            | CNum(id, a, t) ->
                Asm.p("@." + id + "= private constant " + t.p + " " + a.ToString())
        ) consts

    | LLCast(r: R, b: R) ->
        comment(sprintf "%A %A" r b)
        match (r.t.stripType(P0,[]), b.t.stripType(P0,[])) with
        | (Tp(t), Tp(_)) ->
            p(r, "bitcast " + b.t.p + " " + b.p + " to " + r.t.p)
        | (Tp(t), _) ->
            p(r, "inttoptr " + b.t.p + " " + b.p + " to " + r.t.p)
        | (_, Tp(t)) ->
            p(r, "ptrtoint " + b.t.p + " " + b.p + " to " + r.t.p)
        | (Tf, Td) ->
            p(r, "fptrunc " + b.t.p + " " + b.p + " to " + r.t.p)
        | (Td, Td) | (Td, Tf) | (Tf, Td) | (Tf, Tf) ->
            p(r, "fpext " + b.t.p + " " + b.p + " to " + r.t.p)
        | (Td, Ti _) | (Tf, Ti _) ->
            p(r, "sitofp " + b.t.p + " " + b.p + " to " + r.t.p)
        | (Ti _, Td) | (Ti _, Tf) ->
            p(r, "fptosi " + b.t.p + " " + b.p + " to " + r.t.p)
        | (Td, Tu _) | (Tf, Tu _) ->
            p(r, "uitofp " + b.t.p + " " + b.p + " to " + r.t.p)
        | (Tu _, Td) | (Tu _, Tf) ->
            p(r, "fptoui " + b.t.p + " " + b.p + " to " + r.t.p)
        | _ when (Env.size(r.t) = Env.size(b.t)) ->
            p(r, "bitcast " + b.t.p + " " + b.p + " to " + r.t.p)
        | _ when (Env.size(r.t) > Env.size(b.t)) ->
            p(r, "zext " + b.t.p + " " + b.p + " to " + r.t.p)
        | _ ->
            p(r, "trunc " + b.t.p + " " + b.p + " to " + r.t.p)

    | LLNop(s: string) ->
        comment(s)

    | LLJne(r: R, label: string, jmp1: string, jmp2: string) ->
        let reg = GenId.genid("%reg_")
        Asm.p__(reg + " = icmp ne " + r.t.p + " " + r.p + ", 0")
        Asm.p__("br i1 " + reg + ", label %" + jmp1 + ", label %" + jmp2)
        Asm.p(label + ":")

    | LLGoto(label, jmp: string) ->
        Asm.p__("br label %" + jmp)
        if (label <> "") then Asm.p(label + ":")

    | LLLabel(jmp, label: string) ->
        if (jmp <> "") then Asm.p__("br label %" + jmp)
        Asm.p(label + ":")

    | LLPhi(r: R, l1: string, l2: string, t: T, r1: R, r2: R) ->
        p(r, "phi " + t.p + " [" + r1.p + ", %" + l1 + "], [" + r2.p + ", %" + l2 + "]")

    | LLSwitch(n, lbl, cases) ->
        Asm.p__("switch " + n.t.p + " " + n.p + ", label %" + lbl + " [")
        cases |> List.iter (fun (a,b) ->
            Asm.p__("  " + n.t.p + " " + a.p + ", label %" + b))
        Asm.p__("]")

    | LLLoadCStr(r: R, a: String) ->
        let enc = new Text.UTF8Encoding()
        let t = TArr(Ti(8), (int64 (enc.GetByteCount(a)) + 1L))
        let id = GenId.genid("str")
        consts <- CStr(id, a, t) :: consts
        p(r, "bitcast " + Tp(t).p + " @." + id + " to i8*")

    | LLGlobal(r, v) ->
        completeds <- r.id :: completeds
        if (v = RNULL) then
            Asm.p(r.p + "= common global " + r.t.p + " zeroinitializer")
        else
            Asm.p(r.p + "= global " + r.t.p + " " + v.p)
    | LLAssign _ -> raise (TypeError(5002, P0, sprintf "error %A" l))

(**
 * llemitのエントリポイント
 * 
 * @param file: String 出力ファイル名
 * @param ls: ArrayBuffer[LL] 出力LLVM命令リスト
 *)
let apply(file: string, ls: LL list):unit =
    completeds <- []
    Asm.openFile(file)

    List.iter (function
    | (TStr(ls:(string * T) list), r1:R) ->
        let ts = System.String.Join(", ", List.map (function | (_, t1:T) -> t1.p) ls)
        Asm.p(r1.p + " = type { " + ts + " }")
    | (TCls(ls:(string * T) list), r1:R) ->
        let ts = System.String.Join(", ", List.map (function | (_, t1:T) -> t1.pp(r1.p+"*")) ls)
        Asm.p(r1.p + " = type { " + ts + " }")
    | _ -> ()
    ) T.structs

    Asm.p("declare i32 @printf(i8*, ...) nounwind")
    List.iter output ls

    List.iter (fun (id:string, t:T) ->
        match (completeds |> List.tryFind (fun i -> i = id)) with
        | None ->
            match t with
            | TFun(t, p1) ->
                Asm.p("declare " + t.p + " @" + id + "(" + String.Join(", ", List.map (fun (t:T) -> t.p2) p1) + ") nounwind")
            | _ ->
                Asm.p("@"+id+" = external global "+t.p)
        | _ -> ()
        ) globalmap
    
    Asm.close()
