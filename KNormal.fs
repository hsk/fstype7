
(**
 * k正規化処理
 *
 * ProgからLLVM疑似命令のリスト(List[LL])に変換します。
 *)
module KNormal

open AST
open System

(** 出力バッファ *)
let mutable outputBuffer: LL list = []
(** リターンラベル *)
let mutable retLabel: string = null
(** リターン型 *)
let mutable retT: T = Tn
(** ネストしたbreakできる命令のbreakリスト *)
let mutable breaks:string list = []

(** ネストしたcontinueできる命令のcontinueリスト *)
let mutable continues:string list = []


(**
 * LL出力
 * 
 * @param a: LL LLVM命令
*)
let add(a: LL):unit =
    outputBuffer <- a :: outputBuffer

(**
 * 型の種類を "p" "a" "" で返却
 *
 * @param t: T 型
 * @return String 型種別文字列
*)
let rec tName2(t: T): string =
    match t with
    | TDef(id) -> tName2(Env.find(id))
    | TArr _ -> "p"
    | TStr _ -> "p"
    | TFun _ -> "p"
    | Tp _ -> "a"
    | Tr _ -> "a"
    | _ -> ""

(**
 * ローカルレジスタ生成
 *
 * @param t: T 型
 * @return R ローカルレジスタ
 *)
let genRL(t: T): R =
    RL(t, GenId.genid(".."))

(**
 * 値読み込みの変換
 *
 * @param a: R レジスタ
 * @return R 返り値レジスタ
*)
let transLoad(a: R): R =
    match tName2(a.t) with
    | "a" | "p" ->
        let t = Env.find(a.id).stripType([])
        match t with
        | Tp _ ->
            let r = genRL(t)
            add(LLLoad(r, a.setT(Tp(t))))
            r
        | Tr _ -> a.setT(t)
        | TArr(t2, _) ->
            let r = genRL(Tp(t2))
            add(LLCast(r, a.setT(Tp(t))))
            r
        | TFun _ ->
            match a with
            | RL(Tp _ as t, id) ->
                add(LLNop("R1---------"))
                let r = genRL(Tp(t))
                add(LLLoad(r, RL(Tp(t),id)))
                let r2 = genRL(t)
                add(LLLoad(r2, r))
                add(LLNop("R1 AAAAAA"))
                r2
            | RL(t, id) ->
                add(LLNop(sprintf "R2--------- %A" a))
                let r = genRL(t)
                add(LLLoad(r, RL(Tp(t),id)))
                r
            | a -> a
        | t -> a.setT(Tp(t))
    | _ ->
        let r = genRL(a.t)
        add(LLLoad(r, a.setT(Tp(a.t))))
        r

(**
 * ポインタの読み込み
 *
 * @param t: T 型
 * @param e1: R 元のレジスタ
 * @param r: R フィールドを表すレジスタ
 * @return R 返り値レジスタ
 *)
let transALoad(t: T, e1: R, r: R): R =
    match tName2(t) with
    | "a" ->
        let (r0, r1, r2) = (genRL(Tp(t)), genRL(Tp(t)), genRL(t))
        add(LLCast(r0, e1))
        add(LLField(r1, r0, RNULL, r))
        add(LLLoad(r2, r1))
        r2
    | "p" ->
        let (r1, r2) =
            match e1.t with
            | Tp(TArr(t, size)) -> (genRL(Tp(t)), genRL(Tp(t)))
            | t -> (genRL(t), genRL(t))
        add(LLCast(r1, e1))
        add(LLField(r2, r1, RNULL, r))
        r2
    | _ ->
        let (r0, r1, r2) = (genRL(Tp(t)), genRL(Tp(t)), genRL(t))
        add(LLCast(r0, e1))
        add(LLField(r1, r0, RNULL, r))
        add(LLLoad(r2, r1))
        r2


(**
 * 値保存の変換
 *
 * bをaに保存します。
 *
 * @param a: R 保存先レジスタ
 * @param b: R 保存元レジスタ
 * @return R 返り値レジスタ
 *)
let transStore(a: R, b: R): R =
    match tName2(a.t) with
    | "a" ->
        let t = Env.find(a.id)
        let r = genRL(t)
        add(LLCast(r, b))
        add(LLStore(r, a.setT(Tp(t))))
    | _ -> add(LLStore(b, a.setT(Tp(a.t))))
    b


(**
 * ポインタの保存
 *
 * @param t: T 型
 * @param e: R 元のレジスタ
 * @param idx: R インデックスを表すレジスタ
 * @param b: R 保存する値
 * @return R 返り値レジスタ。bを返します
 *)
let transAStore(t: T, e: R, idx: R, b: R): R =
    let (r0, r1) = (genRL(Tp(t)), genRL(Tp(t)))
    add(LLCast(r0, e))
    add(LLField(r1, r0, RNULL, idx))
    add(LLStore(b, r1))
    b

(**
 * 構造体内のフィールドオフセット取得
 *
 * @param t: T 型
 * @param x: String フィールド名
 * @return (T, Any) 検索結果の型と、オフセット値
 *)
let rec getOffset(t: T, x: String) =
    match t.stripType([]) with
    | TStr(m) ->
        let rec ck(m1: (string * T) list, s: int64): (T * int64) =
            match m1 with
            | [] -> raise(Exception(sprintf "error %A is not have %A"  m x))
            | (name, t) :: xs -> if (name = x) then (t, s) else ck(xs, s + 1L)
        ck(m, 0L)
    | Tp(t) -> getOffset(t, x)
    | t -> raise (Exception(sprintf "error %A" t))

(**
 * フィールド取得
 *
 * @param t: T 型
 * @param idx: String 文字列
 * @param a: R 元のレジスタ
 * @return R 返り値レジスタ
*)
let transGetField(t: T, idx: String, a: R): R =
    let (t2, s) = getOffset(t, idx)
    let r2 = genRL(Tp(t2))
    add(LLField(r2, a, RN(Ti(32), "0"), RN(Ti(32), s.ToString())))

    match t2 with
    | Ti(_) | Tu(_) | Tf | Td | Tp(_) | TFun _ ->
        let r1 = genRL(t2)
        add(LLLoad(r1, r2))
        r1
    | _ -> r2

(**
 * フィールド出力
 *
 * @param t: T 型
 * @param idx: String 文字列
 * @param a: R 元のレジスタ
 * @param b: R 設定値のレジスタ
 * @return R 返り値レジスタ。bをそのまま返却
 *)
let transPutField(t: T, idx: String, a: R, b: R): R =
    let (t2, off) = getOffset(t, idx)
    let r = genRL(Tp(t2))
    add(LLField(r, a, RN(Ti(32), "0"), RN(Ti(32), off.ToString())))
    add(LLStore(b, r))
    b

(**
 * LL出力処理
 *
 * eを受け取り、LL出力処理での返り値がある場合はRとして返却する。
 * ネストした式が平たくなります。
 *
 * @param e: E 式
 * @return R 返り値レジスタ
*)
let rec transLocal(e: E): R =
    //add(LLNop("f " + e))
    match e with

    | EVar(p, t, id, c) ->
        t.p |> ignore
        let r = RL(t, id)
        add(LLAlloca(r))
        Env.add(id, t)

        // printfn "knormal %A" envmap
        match c with
        | ENull(_) -> r
        | _ -> transAssign(t, EId(p, t, id), c)

    | ETypeDef(p, t, id) ->
        Env.addTypeDef(id, t)
        RNULL
        
    | ENewArray(p, t, a) ->
        let ft = TFun(Tp(Ti(8)), [Ti(64)])
        let (r, r2, r3) = (genRL(Ti(64)), genRL(Tp(Ti(8))), genRL(t))
        let a2 = transLocal(a)
        add(LLBin(r, "mul", a2, RN(Ti(64), Env.size(t).ToString())))
        add(LLCall(r2, RG(ft, "malloc"), [r]))
        add(LLCast(r3, r2))
        if not(GlobalEnv.contains("malloc")) then GlobalEnv.add("malloc", TFun(Tp(Ti(8)), [Ti(64)]))
        r3

    | ERet(p, t, a) ->
        let l1 = transLocal(a)
        let l2 = GenId.genid("ret")
        if (t <> Tv && t <> Tr(Tv)) then
            add(LLStore(l1, RL(Tp(t), "..retVal")))
            add(LLGoto(l2, "..leave"))
        else
            add(LLGoto(l2, retLabel))
        l1

    | ENew(p, Tp(t)) ->
        let (r, r2) = (genRL(Tp(Ti(8))), genRL(Tp(t)))
        add(LLCall(r, RG(Tp(Ti(8)), "malloc"), [RN(Ti(64), Env.size(t).ToString())]))
        add(LLCast(r2, r))
        if not(GlobalEnv.contains("malloc")) then GlobalEnv.add("malloc", TFun(Tp(Ti(8)), [Ti(64)]))
        r2

    | EGCNew(p, Tp(t)) ->
        let (r, r2) = (genRL(Tp(Ti(8))), genRL(Tp(t)))
        let ft = TFun(Tp(Ti(8)), [Ti(64)])
        add(LLCall(r, RG(ft, "newobj"), [RN(Ti(64), Env.size(t).ToString())]))
        add(LLCast(r2, r))
        GlobalEnv.add("newobj", ft)
        r2

    | ERef(p, t, EId(p2, _, id)) -> Env.findR(id).setT(t)
    | EBlock(p, t, l1) -> List.fold (fun (r:R) (a:E) -> transLocal(a) ) (RN(Tv, "")) l1
    | ESizeOf(p, _, t, _) ->
        let r = genRL(Ti(64))
        add(LLBin(r, "add", RN(Ti(64), "0"), RN(t, Env.size(t).ToString())))
        r
    | ELd(p, t, i) ->
        let r = genRL(t)
        add(LLAssign(r, RN(t, i.ToString())))
        r
    | ELdd(p, t, i) ->
        let r = genRL(t)
        add(LLAssign(r, RN(t, (sprintf "%f" i))))
        r
    | ELds(p, t, i) ->
        let r = genRL(t)
        add(LLLoadCStr(r, i))
        r
    | EBin(p, t, it, op, a, b) ->
        let r = genRL(t)
        add(LLBin(r, op, transLocal(a), transLocal(b)))
        r
    | ENeg(p, t, a) ->
        let r = genRL(t)
        add(LLUnary(r, "neg", transLocal(a)))
        r
    | ENot(p, t, a) ->
        let r = genRL(t)
        add(LLUnary(r, "not", transLocal(a)))
        r
    | EArray _ | EField _ | EPtr _ | EArrow _ | EId _ -> transField(e)
    | EAssign(p, t, a, b) -> transAssign(t, a, b)
    | ECall(p, t, EId(p2, ft, n), l1) when ((not (Env.contains(n))) && GlobalEnv.contains(n)) ->
        let r = genRL(t)
        add(LLCall(r, Env.findR(n), List.map transLocal l1))
        r

    | ECall(p, t, fe, l1) ->
        let l2 = List.map transLocal l1
        let l3 = transLocal(fe)
        let r = genRL(t)
        add(LLCall(r, l3, l2))
        r

    | ENop(p, t, a) ->
        add(LLNop(a)); RNULL
    | ELabel(p, t, a, b) ->
        add(LLLabel("Local._" + a, "Local._" + a))
        transLocal(b)

    | ECast(p, t, a) ->
        let r = genRL(t)
        add(LLCast(r, transLocal(a)))
        r
    | EGoto(p, t, a) ->
        let l = GenId.genid("goto")
        add(LLGoto(l, "Local._" + a))
        RNULL
    | EBreak(p, _) ->
        let b = List.head breaks
        let l = GenId.genid("break")
        add(LLGoto(l, b))
        RNULL
    | EContinue(p, _) ->
        let b = List.head continues
        let l = GenId.genid("continue")
        add(LLGoto(l, b))
        RNULL
    | EIf(p, t, a, b, c) ->
        let id0 = GenId.genid("ok")
        let (id1, l0) = (GenId.genid("else"), GenId.genid("else"))
        let (id2, l1) = (GenId.genid("endif"), GenId.genid("endif"))
        let r = transLocal(a) // cond
        add(LLJne(r, id0, id0, id1))
        let r0 = transLocal(b) // then
        add(LLLabel(l0, l0))
        add(LLGoto(id1, id2))
        let r1 = transLocal(c) // else
        add(LLLabel(l1, l1))
        add(LLGoto(id2, id2))
        if (t <> Tv && r0 <> RNULL && r1 <> RNULL && r0.t = r1.t) then
            let r = genRL(r0.t)
            add(LLPhi(r, l0, l1, t, r0, r1))
            r
        else
            RNULL

    | EWhile(p, t, a, b) ->
        let id0 = GenId.genid("id0")
        let id1 = GenId.genid("while")
        let id2 = GenId.genid("endwhile")
        continues <- id1 :: continues
        breaks <- id2 :: breaks
        add(LLLabel(id1, id1))
        let r = transLocal(a)
        add(LLJne(r, id0, id0, id2))
        transLocal(b) |> ignore
        add(LLGoto(id2, id1))
        continues <- List.tail continues
        breaks <- List.tail breaks
        RNULL

    | EFor(p, t, a, b, c, d) ->
        let id0 = GenId.genid("ok")
        let id1 = GenId.genid("for")
        let id2 = GenId.genid("endfor")
        continues <- id1 :: continues
        breaks <- id2 :: breaks
        transLocal(a) |> ignore
        add(LLLabel(id1, id1))
        let r1 = transLocal(b)
        add(LLJne(r1, id0, id0, id2))
        let r2 = transLocal(d)
        transLocal(c) |> ignore
        add(LLGoto(id2, id1))
        continues <- List.tail continues
        breaks <- List.tail breaks
        r2

    | EDo(p, t, l1, a) ->
        let id1 = GenId.genid("do")
        let id2 = GenId.genid("enddo")
        continues <- id1 :: continues
        breaks <- id2 :: breaks
        add(LLLabel(id1, id1))
        List.iter (fun a -> transLocal a |> ignore)  l1
        let r = transLocal(a)
        add(LLJne(r, id2, id1, id2))
        continues <- List.tail continues
        breaks <- List.tail breaks
        RNULL
(*
    | e @ ESwitch(p, t: T, a: E, cases: List[(E, E)]) ->
        let ra = transLocal(a)
        let lbl = genid("switch")
        let mutable letault = lbl + cases.length
        let (length, ls) = cases.foldLeft(0, List[(R, String)]()) {
            | ((n, ls), (ECase(_, null, _), _)) ->
                letault = lbl + n; (n + 1, ls)
            | ((n, ls), (ECase(_, e, _), _)) -> (n + 1, (transLocal(e), lbl + n) :: ls)
            | a -> throw new Exception(" " + a)
        }
        add(LLSwitch(ra, letault, ls.reverse))
        breaks = lbl + cases.length :: breaks
        for ((n, (_, e)) <- (0 until cases.length).zip(cases)) {
            add(LLLabel(null, lbl + n)); transLocal(e); add(LLGoto(null, lbl + (n + 1)))
        }
        breaks = breaks.tail
        add(LLLabel(null, lbl + cases.length))
        null
*)
    | ESwitch(p, t, a, cases) ->
        let ra = transLocal(a)
        let lbl:string = GenId.genid("switch")+"_"
        let end1:string = lbl+"end"
        breaks <- end1::breaks
        let ff1 (a:bool * int) (b:E * E) :(bool * int) =
            match (a, b) with
            | ((hasDefault,no), (ECase(p, t, ENull(_), _), b)) -> (true, no) // default
            | ((hasDefault,no), (ECase(p, t, a, _), b)) -> // | a: b
                let l3 = transLocal(a)
                let next1 = lbl+"case"+(no+1).ToString()
                let r = genRL(Ti(64))
                add(LLBin(r, "eq", l3, ra))
                add(LLJne(r, next1, lbl+no.ToString(), next1))
                (hasDefault, no + 1)
            | _ -> raise (Exception "error")
        let (hasDefault, letaultno) = List.fold ff1 (false,0) cases
        if (not hasDefault) then
            add(LLGoto(lbl+"_block", end1))
        else
            add(LLGoto(lbl+"_block", lbl+"_letault"))
        let ff (a:int) (b:E * E):int =
            match (a, b) with
            | (no:int, (ECase(p, t, ENull(_), _), b)) -> // letault
                add(LLLabel(lbl + "_letault",lbl + "_letault"))
                transLocal(b) |> ignore
                no
            | (no:int, (ECase(p, t, a, _), b)) ->
                add(LLLabel(lbl + no.ToString(), lbl + no.ToString()))
                transLocal(b) |> ignore
                no + 1
            | _ -> raise(Exception "error")

        // とび先
        List.fold ff 0 cases |> ignore
        breaks <- List.tail breaks
        // 終了
        add(LLLabel(end1, end1))
        RNULL
        
    | _ -> raise(Exception(sprintf "error %A" e))
(**
 * フィールドの変換
 *
 * @param e: E 式
 * @return R 返り値レジスタ
*)
and transField(e: E): R =
    match e with
    | EId(p, t, id) -> transLoad(Env.findR(id))
    | EArray(p, t, e, idx) -> transALoad(t, transField(e), transLocal(idx))
    | EPtr(p, t, e) -> transALoad(t, transField(e), RN(Ti(64), "0"))
    | EField(p, _, t, e, idx) -> transGetField(t, idx, transField(e))
    | EArrow(p, _, t, e, idx) -> transGetField(t, idx, transField(EPtr(p, t, e)))
    | _ -> raise(Exception(sprintf "error %A" e))

(**
 * 代入の変換
 *
 * @param t: T 型
 * @param a: E 代入先の式
 * @param b: E 代入元の式
 * @return R 返り値レジスタ
 *)
and transAssign(t: T, a: E, b: E): R =
    match a with
    | EId(p, _, a) -> add(LLNop(sprintf "EId %A" a)); transStore(Env.findR(a), transLocal(b))
    | EArray(p, t, e, idx) -> transAStore(t, transField(e), transLocal(idx), transLocal(b))
    | EPtr(p, t, e) -> transAStore(t, transField(e), RN(Ti(64), "0"), transLocal(b))
    | EField(p, _, t, e, idx) ->
        let e2 = transField(e)
        let b2 = transLocal(b)
        transPutField(t, idx, e2, b2)
    | EArrow(p, _, t, e, idx) -> transPutField(t, idx, transField(EPtr(p, t, e)), transLocal(b))
    | _ -> raise (Exception(sprintf "error assign %A %A %A" t a b))

(**
 * グローバルな式の変換
 *
 * @param e: E 式
 *
 *)
let transGlobal(e: E):unit =
    match e with
    | EVar(p, t, id, e) ->
        t.p |> ignore
        match (t, e) with
        | (t, ELd(p, _, v)) -> add(LLGlobal(RG(t, id), RN(t, v.ToString())))
        | (t, ELdd(p, _, v)) -> add(LLGlobal(RG(t, id), RN(t, v.ToString())))
        | (TStr _ , (ETuple(p, _, _)as v) ) ->
            let rec p (e:E):string =
                match e with
                | ELd(p, _, v) -> v.ToString()
                | ELdd(p, _, v) -> v.ToString()
                | ETuple(p1, _, ls) -> "{" + String.Join(", ", List.map (fun (l:E) -> l.t.p + " " + p(l)) ls) + "}"
                | _ -> raise (Exception(sprintf "error expression %A" e))
            add(LLGlobal(RG(t, id), RN(t, p(v))))
        | (t, ENull(p)) -> add(LLGlobal(RG(t, id), RNULL))
        | _ -> raise (Exception "error")

    | EFun(p, t, n, prm, b) ->
        Env.init(prm)
        let oldOutputBuf = outputBuffer
        outputBuffer <- []
        let ft = if (n = "main" && t = Tv) then Ti(32) else t
        if (ft <> Tv) then
            Env.add(".retVal", ft)
            add(LLAlloca(RL(ft, "..retVal")))
        
        retLabel <- GenId.genid("leave")
        breaks <- []
        continues <- []
        List.iter (fun (id, t) ->
            add(LLAlloca(RL(t, id)))
            add(LLStore(RL(t, id + ".v"), RL(Tp(t), id)))
        ) prm
        
        let b1 = transLocal(b)
        let r = if (n = "main" && t = Tv) then RN(Ti(32), "0") else b1
        add(LLLabel(retLabel, retLabel))
        let fn = LLFun(ft, n, prm, Env.copy(), List.rev outputBuffer, r)
        outputBuffer <- oldOutputBuf
        add(fn)

    | ETypeDef(p, t, id) -> ()
    | ENop _ -> ()
    | EImport _ -> ()
    | _ -> raise (Exception (sprintf "error global value %A " e))
    //| _ -> raise (TypeError(e.pos, "error global value %A " + e)

(**
 * エントリポイント
 *
 * @param prog プログラム
 * @return ArrayBuffer[LL] 出力LLVM命令リスト
 *)
let apply(prog: Prog): LL list =
    outputBuffer <- []
    //println(e)
    match prog with
    | Prog(ls) -> List.iter transGlobal ls
    List.rev outputBuffer
