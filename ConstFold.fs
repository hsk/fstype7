(**
 * 定数畳み込み処理
 *)

module ConstFold

open AST
open System

(**
 * 定数畳み込みクラス
 *
 * 例) a=1+2 f(a)を f(3)に書き換えます。
 *)
type ConstFold(parent: Option<ConstFold>) =

    (** 定数畳込用の環境 *)
    let mutable map = new Map<string, R>([])

    (** 出力用バッファ *)
    let mutable outputBuffer:LL list = []

    (**
     * レジスタ展開
     * 
     * 環境にRがあれば、そのRを返しなければ、引数をそのまま返します。
     * 親の環境も検索します。
     *)
    member this.expand(v: R): R =
        if (v = RNULL) then v
        else if (map.ContainsKey(v.id)) then this.expand(match map.TryFind(v.id) with | Some(a) -> a | None -> v )
        else match parent with | Some(p) -> p.expand(v) | None -> v
    (**
     * Rのリストを展開します
     *)
    member this.expandList(prms: R list): R list = List.map this.expand prms

    (**
     * 畳み込み処理の本体
     * 
     * @param ls: ArrayBuffer[LL] LLリスト
     * @return ArrayBuffer[LL] 畳み込み後のリスト
     *)
    member this.fold(ls: LL list): LL list =

        
        (**
         * 出力
         *)
        let add(ll:LL):unit =
            outputBuffer <- ll :: outputBuffer

        let f l = 
            match l with
            | LLCall(id, op, prms) -> add(LLCall(id, op, this.expandList(prms)))
            | LLBin(id, op, a, b) ->
                let a1 = this.expand(a)
                let b1 = this.expand(b)
                match (op, a1, b1) with
                | ("sub", RN(Ti(_), a), RN(Ti(_), b)) -> map <- map.Add(id.id, RN(id.t, (Convert.ToInt64(a) - Convert.ToInt64(b)).ToString()))
                | ("add", RN(Ti(_), a), RN(Ti(_), b)) -> map <- map.Add(id.id, RN(id.t, (Convert.ToInt64(a) + Convert.ToInt64(b)).ToString()))
                | ("mul", RN(Ti(_), a), RN(Ti(_), b)) -> map <- map.Add(id.id, RN(id.t, (Convert.ToInt64(a) * Convert.ToInt64(b)).ToString()))
                | _ -> add(LLBin(id, op, a1, b1))

            | LLUnary(a, b, c) -> add(LLUnary(a,b, this.expand(c)))
            | LLAssign(s, d) -> map <- map.Add(s.id, d)
            | LLAlloca(id: R) -> add(LLAlloca(this.expand(id)))
            | LLField(id, id2, id3, id4) -> add(LLField(id, this.expand(id2), this.expand(id3), this.expand(id4)))
            | LLStore(id1, id2) -> add(LLStore(this.expand(id1), this.expand(id2)))
            | LLLoad(id1, id2) ->
                let id22 = this.stripPointerT(this.expand(id2))
                if (this.expand(id2) <> id2) then
                    map <- map.Add(id1.id, id22)
                else
                    add(LLLoad(this.expand(id1), this.expand(id2)))
            | LLCast(did, sid) -> add(LLCast(this.expand(did), this.expand(sid)))
            | LLSwitch(n, lbl, cases: (R * string) list) ->
                add(LLSwitch(this.expand(n), lbl, List.map (fun (r, s) -> (this.expand(r), s)) cases))
            | LLLabel _ -> add(l)
            | LLGoto _ -> add(l)
            | LLFun(t, n, p, env, ls, r) ->
                let cf = new ConstFold(Some(this))
                add(LLFun(t, n, p, env, cf.fold(ls), cf.expand(r)))
            | LLNop _ -> add(l)
            | LLJne(r, a, b, c) -> add(LLJne(this.expand(r),a,b,c))
            | LLPhi(reg: R, l1: string, l2: string, t: T, r1: R, r2: R) ->
                add(LLPhi(this.expand(reg), l1, l2, t, this.expand(r1), this.expand(r2)))
            | LLGlobal(s, d) -> add(l)
              (*
              kNormal.tName2(s.t) match {
                | "" -> map = map + (s.id -> d)
                | _ ->
              }
              add(l)*)
            | LLLoadCStr _ -> add(l)

        List.iter f ls
        List.rev outputBuffer
  

    (**
     * 型の変換
     *
     * ポインタの型は内部の型を取り出して返却します。
     *)
    member this.stripPointerT(a: R): R =
        match KNormal.tName2(a.t) with
        | "a" | "p" when(map.ContainsKey(a.id)) ->
            match map.Item(a.id).t.stripType([]) with
            | Tp(t2) -> a.setT(t2)
            | Tr(t2) -> a.setT(t2)
            | TArr(t2, _) -> a.setT(t2)
            | TFun _ -> a
            | _ -> a
        | t -> a

(**
 * エントリポイント
 *)
let apply(ls: LL list): LL list =
    let cf = new ConstFold(None)
    cf.fold(ls)
