(**
 * 型チェック
 *)

module Typing

open AST
open System

(**
 * 暗黙の型変換付きの型付け処理
 *
 * @param e: Ebin
 * @param a1: E
 * @param b1: E
 * @return E
 *)
let autoCastBinT(e: E, a1: E, b1: E): E =
    
    let rec implicitConversion(a: E, b: E): (E * E) =
        match (a.t, b.t) with
        | (t1, t2) when (t1 = t2 && Tn <> t1) -> (a, b)
        | (Td, (Tf | Ti(64))) -> (a, ECast(b.pos, Td, b))
        | ((Tf | Ti(64)), Td) -> (ECast(a.pos, Td, a), b)
        | (Tf, Ti(64)) -> (a, ECast(b.pos, Tf, b))
        | (Ti(64), Tf) -> (ECast(a.pos, Tf, a), b)
        | (Tp(_) as t1, _) -> (a, ECast(b.pos, t1, b))
        | (_, Tp(_)) -> (a, b)
        | (Ti(64), _) -> implicitConversion(a, ECast(b.pos, Ti(64), b))
        | (_, Ti(64)) -> implicitConversion(ECast(a.pos, Ti(64), a), b)
        | (Ti(32), _) -> implicitConversion(a, ECast(b.pos, Ti(32), b))
        | (_, Ti(32)) -> implicitConversion(ECast(a.pos, Ti(32), a), b)
        | (Ti(16), _) -> implicitConversion(a, ECast(b.pos, Ti(16), b))
        | (_, Ti(16)) -> implicitConversion(ECast(a.pos, Ti(16), a), b)
        | _ -> (a, b)

    let (a, b) = implicitConversion(a1, b1)
    let e2 =
        match (e, a.t, b.t) with
        | (EBin(p,t,ta,op,_,_), t1, t2) when (t1 = t2) -> EBin(p, t1, ta, op, a, b)
        | (EBin(p,t,ta,op,_,_), Tp(t1), _) -> EBin(p, Tp(t1), ta, op, a, b)
        | (EBin(p,t,ta,op,_:E,_), Tn, t1) ->
            printfn "kore 1 %A %A" a.pos b.pos
            EBin(p, t1, ta, op, a.setT(t1), b)
        | (EBin(p,t,ta,op,_,_), t1, Tn) ->
            printfn "kore 2 %A %A" a.pos b.pos
            EBin(p, t1, ta, op, a, b.setT(t1))
        | _ -> raise(TypeError(3001, e.pos, "error"))
    // 比較演算子の場合返り値はTlとする
    let rc =
        match e2 with
        | EBin(p, t, _, op, a, b) ->
            match op with
            | "eq" | "ne" | "gt" | "lt" | "ge" | "le" -> EBin(p, Ti(64), t, op, a, b)
            | _ -> EBin(p, t, t, op, a, b)
        | _ -> raise(TypeError(3002, e2.pos, "error"))
    rc

(**
 * ２つの式の型を合わせる代入時処理
 *
 * @param f: EAssign
 * @param a: E
 * @param b: E
 * @return E
 *)
let unifyBinT(f: E, a: E, b: E): E =

    //printfn "unifyBinT\nf=%A\na=%A\nb=%A" f a b
    match (a.t, b.t) with
    // aとbが同じなら親も同じにする
    | (t1, t2) when (t1.stripType(a.pos, []) = t2.stripType(b.pos, [])) -> EAssign(f.pos, t1, a, b)
    // bがlongならaに合わせる a = 1+5 みたいな処理のaがbyteだったら、byteに勝手に変換しちゃうよと。
    | (ta, Ti(64)) -> EAssign(f.pos, ta, a, ECast(b.pos, ta, b))
    // floatとdoubleならfloatにする doubleな値は、変数に合わせてしまう。合わせてしまうのは良いけど、キャスト演算が入ってるの？
    | (Tf, Td) -> EAssign(f.pos, Tf, a, ECast(b.pos, Tf, b))
    // aがポインタなら親もポインタ
    | (Tp(t1), Tn) -> EAssign(f.pos, Tp(t1), a, b)
    | (Tp(t1), TArr(t2, _)) -> EAssign(f.pos, Tp(t1), a, b)
    | (Tp(t1), Tp(t2)) when (t1 = t2) -> EAssign(f.pos, Tp(t1), a, b)
    | (TArr(t1, _), Tp(t2)) when (t1 = t2) -> EAssign(f.pos, Tp(t1), a, b)
    // 片方の型が決まっていなければコピーする
    | (Tn, t1) ->
        raise(TypeError(3003, a.pos, sprintf "kore 3 %A" b.pos))// p(f, f.copy(t1, setT(a, t1), b))
    | (t1, Tn) ->
        raise(TypeError(3004, a.pos, sprintf "kore 4 %A" b.pos))// p(f, f.copy(t1, a, setT(b, t1)))
    | (t1, t2) -> raise(TypeError(3005, a.pos, sprintf "type error %A %A %A %A" b.pos a t1 t2))

(**
 * return type of function
 *)
let mutable funType: T = Tn

let typingTypeDef(id:string, t:T):T =
    match t with
    | TCls(ls) ->
        let rec memcnv ls rls =
            match ls with
            | [] -> rls
            | (a,TDlg(t1,_,dls))::ls -> memcnv ls ((a,TDlg(t1,Tp(TDef(id)),Tp(TDef(id))::dls))::rls)
            | (a,t)::ls -> memcnv ls ((a,t)::rls)
        TCls(memcnv ls [])
    | t -> t


(**
 * ローカル変数の型付け
 *
 * 式の型が決まっていない場合に、子の型から型を決定する
 * 基本的にトップダウンで末端まで行って型を取得してトップまで合わせるだけになっている。
 * TODO: トップの型とのチェックはしていないので、チェックする
 *
 * @param pt: T
 * @param e: E
 * @return E
 *)
let rec typingLocal(pt: T, e: E): E =

    let typingLocalVar(p:P, t:T, a:string, c:E, f:(P * T * string * E)->E):E =
        match (t, c) with    
        | (_, ENull(_)) -> // ローカル環境に型を保存する
            if (Env.contains(a)) then
                raise(TypeError(3008, e.pos, a + " is already defined"))
            // これはtypedefではないのだけど、addtypedefになってるけど、addはローカル変数のアドレス計算もするのでコレでok
            Env.addTypeDef(a, t)
            e
        // 配列リテラル
        | (_, ECall(pc, _, (EId(idp, _, "Array") as eda), ls)) ->
            if (Env.contains(a)) then
                raise(TypeError(3009, e.pos, a + " is already defined"))
            let (tt, t1) =
                match t with
                | TArr(t1, size) ->
                    if (size <> (int64 ls.Length)) then
                        raise (TypeError(3010, e.pos, "array size dont match"))
                    (t, t1)
                | Tn ->
                    let t1 = typingLocal(Tn, List.head ls).t
                    (TArr(t1, (int64 ls.Length)), t1)
                | _ -> raise (TypeError(3011, p, "error"))

            let ff (i, l) a1 =
                    (i + 1L, EAssign(p, t1, EArray(p, t1, EId(p, tt, a), ELd(p, Ti(32), i)), typingLocal(t1, a1)) :: l)
            let (n, l) = List.fold ff (0L, []) ls
            Env.addTypeDef(a, tt)
            EBlock(p, t, f(p, tt, a, ENull(p)) :: (List.rev l))

        // var a = 1 型推論
        | (Tn, _)->
            if Env.contains(a) then
                raise(TypeError(3012,e.pos, a + " is already defined "))
            let c2 = typingLocal(pt, c)
            if c2.t = Tv then
                raise(TypeError(3021,e.pos, a + " type void error "))
            
            Env.addTypeDef(a, c2.t)
            f(p, c2.t, a, c2)
        | _ ->
            //if (env.map.getOrElse(a, null) != null) {
            //    throw TypeError(e.pos, a + " is already defined ")
            //}
            let c2 =
                match c with
                | ELdd (p, _,a) -> ELdd(p,t,a)
                | ELd (p,_,a) -> ELd(p,t,a)
                | _ ->
                    let c2 = typingLocal(pt, c)
                    if (t <> c2.t) then raise(TypeError(3013,e.pos, (sprintf "type match error %A and %A" t c2.t)))
                    else c2
            
            Env.addTypeDef(a, t)
            f(p, t, a, c2)
        

    match e with
    | EFun(p, t, id, p1, b) ->
        // 関数内関数はエラー
        raise (TypeError(3006, e.pos, "inner function is not supported"))
    | EMethod(p, t, id, p1, b) ->
        // 関数内methodはエラー
        raise (TypeError(3006, e.pos, "inner method is not supported"))
    | ETypeDef(p, t, id) -> // ローカル環境に型を保存する。
        if (Env.contains(id)) then
            raise(TypeError(3007, e.pos, id + " is already defined"))
        let t2 = typingTypeDef(id, t)
        //raise(Exception(sprintf "etypedef %A %A" e t2))
        //printfn "addTypeDef id=%s t= %A t2=%A" id t t2         
        Env.addTypeDef(id, t2)
        ETypeDef(p, t2, id)
    // var a:t = f
    | EVar(p, t, a, c) -> typingLocalVar(p,t,a,c, EVar)
    | EVal (p, t, a, c) ->
        Env.addVal(a)
        typingLocalVar(p,t,a,c, EVal)
        
    // ここからが文。式との違いは、親が値を求めていないかもしれないと言う事で、必要ない時は値を消す処理をどこかでする必要がある。
    // 親が求めている型は分からないので何ともならないけどw
    // 親が求める型に合わせて、popする式を入れるのは手だろうなと思うのと、そうするとよりunifyな感じになるよなと。
    | EBlock(p, _, b: E list) ->
        let rec loop(l: E list, r: E list): E =
            match l with
            | [] -> EBlock(p, Tv,[])
            | [x] ->
                let y = typingLocal(pt, x)
                EBlock(p, y.t, (y :: r) |> List.rev) // 最後の値をブロックの型にする
            | x :: xs -> loop(xs, typingLocal(Tv, x) :: r)
        loop(b, [])

    | EWhile(p, t: T, e: E, s: E)->
        EWhile(p, Tv, typingLocal(Tv, e), typingLocal(Tv, s))
    | EFor(p, t: T, i: E, c: E, n: E, s: E) ->
        EFor(p, Tv, typingLocal(Tv, i), typingLocal(Ti(64), c), typingLocal(Tv, n), typingLocal(pt, s))
    | EDo(p, t: T, a: E list, b: E) ->
        EDo(p, Tv, a |> List.map (fun e -> typingLocal(Tv, e)), typingLocal(Ti(64), b))
    | ESwitch(p, t: T, a: E, b: (E * E) list) ->
        // switchの値は最後のブロックの値にしてみてるけどテストが甘いはず breakがあるから,voidにしておく
        let a2 = typingLocal(Tn, a)
        let b2 = b |> List.map (fun (a:E, e:E) ->
            let a3 = typingLocal(a2.t, a)
            let e2 = typingLocal(Tv, e)
            (a3, e2)
        )
        ESwitch(p, Tv, a2, b2)
    | EIf(p, _, a: E, b: E, c: E) ->
        let a2 = typingLocal(Ti(64), a)
        let b2 = typingLocal(Tn, b)
        let c2 = typingLocal(Tn, c)
        let t =
            match (b2.t, c2.t) with
            // ifの型は片方がvoidならvoid
            | (Tv, _) -> Tv
            | (_, Tv) -> Tv
            // trならtrじゃないほう
            | (Tr _, b) when (match b with | Tr _ -> false | _ -> true) -> b
            | (a, Tr _) when (match a with | Tr _ -> false | _ -> true) -> a
            // aとbが違う型のときもvoid // castできたとしてもvoid
            | (a, b) -> if (a = b) then a else Tv
        EIf(p, t, ECast(a2.pos, Ti(64), a2), b2, c2) // 位置情報もコピーされる

    // voidはない copy使って位置情報も全部コピー
    // 決まって無い時はlong. intじゃないの？って話もあるけど、64bitだしlong
    // 決まってたらそのまま
    | ELd(p, t, i) ->
        match (pt, t) with
        | (Tv, Tn) -> ELd(p, Ti(64), i)
        | (Tn, Tn) -> ELd(p, Ti(64), i)
        | (Ti(_), Tn) -> ELd(p, pt, i)
        | _ -> e
    // double
    | ELdd(p, t, i: double) ->
        match (pt, t) with
        | (Tv, Tn) -> ELdd(p, Td, i)
        | (Tn, Tn) -> ELdd(p, Td, i)
        | (Tf, Tn) | (Td, Tn) -> ELdd(p, pt, i)
        | (_, Tn) -> ELdd(p, Td, i)
        | _ -> e
    | ELds(p, t, i: string) ->
        let pt2 = pt.stripType(p, [])
        match (pt2, t) with
        | (Tv, Tn) -> ELds(p, Tp(Ti(8)),i)
        | (Tn, Tn) -> ELds(p, Tp(Ti(8)),i)
        | (Tp(Ti(8)), Tn) -> ELds(p, pt,i)
        | (Tp(Tu(8)), Tn) -> ELds(p, pt,i)
        | _ ->
            raise (TypeError(3015,p,"dame " + pt2.ToString() + " " + t.ToString()))
    | ENeg(p, t: T, a: E) ->
        let a2 = typingLocal(pt, a)
        ENeg(p, a2.t, a2)
    | EBin(p, t: T, it: T, i, a: E, b: E) ->
        autoCastBinT(e, typingLocal(pt, a), typingLocal(pt, b))
    | EAssign(p, t, a: E, b: E) ->
        match a with
        | EId(p,t,id) ->
            if(Env.checkVal(id)) then
                raise(TypeError(3041,p,sprintf "cannot assign val value %s" id))
            else ()
        | _ -> ()
        
        // printfn "EAssign pt=%A %A" pt e
        let rc = unifyBinT(e, typingLocal(pt, a), typingLocal(pt, b))
        // printfn "EAssign rc=%A" rc
        rc
    | ENot(p, t: T, a: E) ->
        let a2 = typingLocal(Ti(64), a)
        ENot(p, a2.t, a2)
    | ESizeOf(p, _, _, ENull(_)) -> e
    | ESizeOf(p,_, _, a) ->
        let a2 = typingLocal(Ti(64), a)
        ESizeOf(p, Ti(64), a2.t, ENull(a2.pos))
    | ENewArray(p, t: T, a: E) -> ENewArray(p, t, typingLocal(Ti(64), a))
    | ENew(p, t: T, a:E list) ->
        let a2 = List.map (fun a -> typingLocal(Tn, a)) a
        ENew(p, t, a2)
    | EGCNew(p, t: T) -> e
    | ERef(p, t: T, a: E) ->
        let a2 = typingLocal(Tn, a)
        ERef(p, Tp(a2.t), a2)
    | EPtr(p, t: T, a: E) ->
        let a2 = typingLocal(Tn, a)
        match a2.t.stripType(p, []) with
        | Tp(t) -> EPtr(p, t, a2)
        | TArr(t, _) -> EPtr(p, t, a2)
        | t -> raise(TypeError(3016,p, "error " + t.ToString()))
    | EGoto(p, t: T, a: string) -> EGoto(p, Tv, a)
    | ELabel(p, t: T, a: string, b) ->
        let b2 = typingLocal(Tn, b)
        ELabel(p, b2.t, a, b2)
    | ECase(p, t: T, ENull(_), b) -> e
    | ECase(p, t: T, a, b) ->
        let a2 = typingLocal(pt, a)
        if (a2.t <> pt) then
            ECase(p, pt, ECast(p, pt, a2), b)
        else
            ECase(p, a2.t, a2, b)
    | ENop(p, t: T, s: String) -> e
    | EBreak(p, t: T) -> e
    | EContinue(p, t: T) -> e
    | ECast(p, t: T, a) -> ECast(p, t, typingLocal(Tn, a))
    | ERet(p, t: T, a: E) ->
        let a2 = typingLocal(funType, a)
        if (funType <> a2.t) then
            raise(TypeError(3017, e.pos, "return type error. expected type is " +
                            funType.ttos + " but found " + a2.t.ttos + " " + e.ToString()))
        ERet(p, Tr(a2.t), a2)
    // 変数
    | EId(p, t, id: string) ->
        match t with
        | Tn ->
                try
                    let t2 = Env.mapfind(p, id)
                    if (t2 = Tn) then
                        raise (TypeError(3018, e.pos, "found undefined id '" + id + "'"))
                    EId(p, t2, id)
                with
                | _ ->
                    try
                        let ts = Env.mapfind(p, "this")
                        typingLocal(pt, EField(p, Tn, t, EId(p,t,"this"), id))
                    with
                    | _ ->
                        let t2 = GlobalEnv.mapfind(p, id)
                        if (t2 = Tn) then
                            raise (TypeError(3018, e.pos, "found undefined id '" + id + "'"))
                        EId(p, t2, id)

            // 型が決まらなかったらエラー
            
        | _ -> e

    | EArray(p, t: T, id: E, idx: E) ->
        let id2 = typingLocal(Tn, id)
        let rec aa(t: T): T =
            match t with
            | TDef(n) -> aa(Env.find(p, n))
            | TArr(t, s) -> t
            | Tp(t) -> t
            | t -> t
        EArray(p, aa(id2.t), id2, typingLocal(Ti(64), idx))

    | EField(p, t: T, t1, a: E, id: string) ->
        let a2 = typingLocal(t1, a)
        let rec f(t: T): T = 
            //printfn "f t = %A envmap %A" t envmap
            match t with
            | TDef(id) -> f(Env.find(p, id))
            | TStr(m) ->
                match List.tryFind (fun (s,_) -> s = id) m with
                | None ->
                    raise( TypeError(3019, p, "type " + a2.t.ttos + " not have " + id))
                | Some(s,t) -> t 
            | TCls(m) ->
                //printfn "a=%A a2=%A m=%A" a a2 m
                match List.tryFind (fun (s,_) -> s = id) m with
                | None ->
                    raise( TypeError(3042, p, "type " + a2.t.ttos + " not have " + id))
                | Some(s,t) -> t 
            | Tp(t1) -> f(t1)
            | _ -> raise( TypeError(3020,p,"error"))
        EField(p, f(a2.t), a2.t, a2, id)
    | ECall(pos, t: T, a1: E, ls: E list) ->
        let a2 = typingLocal(Tn, a1)
        let rec checkTypes(n: int, as1: T list, ps: E list, rs: E list): E list =
            match (as1, ps) with

            | ([], []) -> rs
            | (a :: as1, p :: ps) ->
                let p2 = typingLocal(a, p)

                if (a.stripType(pos, []) <> p2.t.stripType(pos, [])) then
                    match a1 with
                    | EId(p1, t, id) ->
                        raise(TypeError(3025, a1.pos, n.ToString() + "th parameter type check error " + id + ":" +
                                        a2.t.ttos + " found:" + p2.t.ttos + " expected:" + a.ttos))
                    | _ ->
                        raise(TypeError(3026, a1.pos, n.ToString() + "th parameter type check error " + a1.ToString() + " " +
                                        a2.t.ttos + " " + p2.t.ttos + " " + a.ttos))
                checkTypes(n + 1, as1, ps, p2 :: rs)
            | _ ->
                raise(TypeError(3027, a1.pos, n.ToString() + "th parameter undefined function " + a1.ToString() + " a2.t=" + a2.t.ttos))
        let (ft, t2, prms) =
            match a2.t with
            | TFun(t2, prms) as ft -> (ft,t2, prms)
            | Tp(TFun(t2, prms) as ft) -> (ft,t2, prms)
            | TDlg(t2, ct, prms) as ft-> (ft,t2, prms)
            | Tp(TDlg(t2, ct, prms) as ft) -> (ft,t2, prms)
            | _ ->
                raise (TypeError(3028, a1.pos, "error undefined function " + a1.ToString() + " a2.t=" + a2.t.ttos))
        match ft with
        | TFun _ ->
            ECall(pos, t2, a2, checkTypes(1, prms, ls, []) |> List.rev)
        | TDlg _ ->
            let a3 = typingLocal(Tn, a2)
            let (a4,ls2) =
                match a3 with
                | EField(p,TDlg(t1,_,ls1),t2, e, m) ->
                    (EField(p,TDlg(t1,t2,ls1),t2,e,m), e::ls)
                | _ -> raise(Exception(sprintf "%A" a3))//(a3,ls)
            let e2 = ECall(pos, t2, a4, checkTypes(1, prms, ls2, []) |> List.rev)

            e2
    (*
    | e@ECall(t: T, a: E, ls: E list) ->
        let a2 = f(Tn, a)
        a2.t match {
            | TFun(t2, _) ->
                    let ls2 = ls.map(f(Tn,_))
                    p(e, e.copy(t2, a2, ls2))
            | _ -> throw TypeError(3029, "error undefined function " + a);
        }*)
    | ENull(p) -> e
    | EImport(p,_) -> raise(TypeError(3030,p, "can't use import in function"))
    | ETuple(p,_,_) -> raise(TypeError(3031,p, "can't use tuple this place"))

let typingGlobalVar(ecopy: (P * T * string * E) -> E, ep: P, t: T, b: String, c: E): (string * T * E) =
    if (Env.contains(b)) then
        raise( TypeError(3032, ep, b + " is already defined "))

    match (t, b, c) with
    | (Tn, b, c) ->
        let c2 = typingLocal(Ti(64), c)
        (b, c2.t, ecopy(ep, c2.t, b, c2))

    // var a:int = 1 型が決まっている整数
    | (t, a, ELd(pe,_, c)) ->
        (a, t, ecopy(ep, t, a, ELd(pe, t, c)))

    // var a:float = 1.0 固定のdouble値
    | (t, a, (ELdd(pd, _, c) as ed)) ->
        (a, t, ecopy(ep, t, a, ELdd(pd,t, c)))

    // 文字列
    | (t, a, (ELds(pd, _, c) as ed)) ->
        (a, t, ecopy(ep, t, a, ELds(pd, t, c)))

    // タプル
    | (t, a, (ETuple(pd, _, c) as ed)) ->
        match t.stripType(ep, []) with
            | TStr(ts) as t ->
                let rec cpType(a: E list, ts: (string * T) list): E list =
                    match (a, ts) with
                    | ([], []) -> []
                    | (a :: as1, (s, t) :: ts) -> (a.setT(t)) :: cpType(as1, ts)
                    | _ -> raise(TypeError(3033,ep,"error"))
                (a, t, ecopy(ep, t, a, ETuple(pd, t, cpType(c, ts))))
            | _ -> raise(TypeError(3034, ep, a + " type unmatch"))
    | _ -> raise(TypeError(3035, ep, "error"))

let mutable imports:string list = []


(**
 * トップレベルの型付け
 * function以外は環境に取り込み済みなので、関数内部のみ処理する
 * 
 * @param e: E
 * @return E
 *)
let typingGlobal(e: E): E =
    // printfn "f %A" e
    match e with
    | EFun(p, t, id, p1, b) ->
        // 関数の型で環境を初期化
        Env.init(p1)
        funType <- t // 関数の型チェック用。
        let b2 = typingLocal(t, b)
        match (t.stripType(p,[]), b2.t.stripType(p,[])) with
            | (Tv, a) -> ()
            | (t, Tr(a)) ->
                if (t <> a) then
                    raise(TypeError(3036, e.pos,
                                   "error function " + id +
                                   " type error type=" + t.ttos + 
                                   " return type " + b2.t.ttos + " " + b2.ToString()))
            | (t, a) ->
                if (t <> a) then
                    raise (TypeError(3037, e.pos, "error function " + id +
                                    " type error type=" + t.ttos + " return type " + b2.t.ttos + " " + b2.ToString()))
        EFun(p, t, id, p1, b2)
    | EMethod(p, t, id, p1, b) ->
            raise (TypeError(3006, e.pos, "cannot use global method"))
    // TODO: 関数の型が未定義なら、コピーすると型推論出来るので推論できるけど、定義がないので困るので推論しない。
    | EVar(p, t: T, id: string, ENull(_)) -> // ローカル環境に型を保存する
        if Env.contains(id) then
            raise(TypeError(3038, e.pos, id + " is already defined env "))
        // これはtypedefではないのだけど、addtypedefになってるけど、addはローカル変数のアドレス計算もするのでコレで宵。
        // TODO: もしかすると、addでタイプを保存して、addVarで変数の計算ってやったほうがいいのかも。
        GlobalEnv.add(id, t); e

    // var a = 1 
    | EVar(p, t, b, c) ->
        let (b1, t1, e1) = typingGlobalVar(EVar, p, t, b, c)
        GlobalEnv.add(b1, t1)
        e1
    | EVal(p, t, b, c) ->
        let (b1, t1, e1) = typingGlobalVar(EVal, p, t, b, c)
        GlobalEnv.add(b1, t1)
        GlobalEnv.addVal(b1)
        e1
    | EImport _ -> e
    | ETypeDef(p,t,id) -> ETypeDef(p, typingTypeDef(id, t), id)
    
    | ENop _ -> e
    | e -> raise (TypeError(3039,e.pos,"error " + e.ToString())) // スルー

(**
 * グローバルな型チェック
 *
 * グローバルな関数と変数を環境テーブルに保存します。
 *
 * 先に型を調べる事で、前方参照が可能になります。前方とはソースコードの下方向です。
 * 使用する前に定義されていない型を使えるようにするために、先にソース全体の型だけチェックしてしまいます。
 *)
let rec checkGlobalType(e: Prog):unit =
    let f e =
        match e with
        // 関数の型を環境に保存
        | EFun(p, t, n, prm, b) ->
            GlobalEnv.add(n, TFun(t, List.map (fun (id, t) -> t ) prm))
        // 型の宣言を環境に保存
        
        | ETypeDef(p, t, id) ->
            GlobalEnv.addTypeDef(id, typingTypeDef(id, t))
       // 型の指定のないグローバル変数は式の型を変数の型にして環境に保存
        | EVar(p, Tn, a, c) ->
            let c2 = typingLocal(Tn, c)
            GlobalEnv.add(a, c2.t)
        // 変数を環境に保存
        | EVar(p, t, id, a) ->
            GlobalEnv.add(id, t)
        | EVal(p, Tn, a, c) ->
            let c2 = typingLocal(Tn, c)
            GlobalEnv.add(a, c2.t)
            GlobalEnv.addVal(a)
        // 変数を環境に保存
        | EVal(p, t, id, a) ->
            GlobalEnv.add(id, t)
            GlobalEnv.addVal(id)

        // 何かの残骸は読み捨て
        | ENop _ -> ()
        | EImport(p, id) -> importFile(p, id + ".lll")
        | e ->
            raise(TypeError(3040, e.pos, sprintf "syntax error found unexpected expression in global scope %A" e))
    match e with
    | Prog(b) -> List.iter f b

and importFile(p:P, file:string):unit =
        
    // 再度読み込み防止
    match imports |> List.tryFind (fun a -> file = a) with
    | Some(_) ->
        ()
    | None ->
        try
            let src = Exec.readAll(file)
            // パース
            let st = Compact.parse(src)
            let ast = Transduce.apply(st)

            imports <- file::imports
            // 型付け
            checkGlobalType(ast)
        with
            | :? System.IO.DirectoryNotFoundException -> raise(TypeError(3043, p, "file not found "+file))
            | :? System.IO.FileNotFoundException -> raise(TypeError(3043, p, "file not found "+file))
        ()

(**
 * 型チェック本体
 *)
let apply(e: Prog): Prog =
    // 初期化
    Env.init([])
    // グローバルな型をチェック
    checkGlobalType(e)
    // 型をチェック、チェック、ダブルチェックだ。ぜんぜんチェックしてないけど。上からと下からチェックで正確になるんでしょうねと。
    // で、横のつながりを持たせるには、型変数を導入してやって、情報伝達してやるといいわけだけけど、そこまではしない方針ですっと。
    match e with
    | Prog(b) -> Prog(List.map typingGlobal b)
