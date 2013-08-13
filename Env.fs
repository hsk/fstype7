(**
 * 環境
 *)
module Env

open AST
open System

(** val list *)
let mutable envVals:string list = []

(**
 * 環境のコピー
 *)
let copy(): (string *T) list * string list = (envmap, envVals)

(**
 * 環境の読み込み
 *)
let load(e: (string *T) list * string list):unit =
    match e with
    | (e,v) ->
        envmap <- e
        envVals <- v
(**
 * 環境の初期化
 *)
let init(p: (string *T) list):unit =
    load(p,[])

(**
 * シンボル検索
 *)
let find(p:P, id:string):T =
    try
        let (_, b) = List.find (function | (id2, t) -> id = id2) envmap
        b
    with
        e ->
            GlobalEnv.mapfind(p, id)

(**
 * シンボル検索
 *)
let contains(id:string):bool =
    try
        List.find (function | (id2, t) -> id = id2) envmap |> ignore
        true
    with
        e -> false

let mapfind(p:P, id:string):T = find(p, id)

(**
 * 検索してレジスタで返却
 *)
let findR(p:P, id: string):R =
//    printfn "%A" envmap
    if contains(id) then
        RL(find(p, id),id)
    else
        try
            RG(GlobalEnv.mapfind(p, id),id)
        with
        | e -> raise(TypeError(3701, P0, "not found "+id))

(**
 * 型定義追加
 *)
let addTypeDef(id: string, t: T):unit =
    envmap <- (id, t) :: envmap

let getFieldNo(p:P, id: string, field: string):int =
    let rec getNo(no:int, m:(string * T) list):int =
        match m with
        | [] -> raise (TypeError(3702, P0, "not found " + field))
        | (name,t)::xs when (name = field) -> no
        | x::xs -> getNo(no + 1, xs)
    match mapfind(p, id) with
    | TStr(m) -> getNo(0, m)
    | TCls(m) -> getNo(0, m)
    | _ -> raise(TypeError(3703, P0, "error"))

(**
 * 型の追加
 *)
let add(id: string, t: T):unit =
    envmap <- (id, t) :: envmap
    t.p |> ignore

(**
 * サイズ計算
 *)
let rec size(p:P, t: T): int64 =
    match t with
    | Ti(i) -> (int64 i) / 8L
    | Tu(i) -> (int64 i) / 8L
    | Tf -> 4L
    | Td -> 8L
    | Tp(_) -> 8L
    | TDef(id) -> size(p, find(p, id)) 
    | TArr(t, s) -> size(p, t) * s
    | TStr(m) -> List.fold (fun a (t, b) -> a + size(p, b)) 0L m
    | TCls(m) -> List.fold (fun a (t, b) -> a + size(p, b)) 0L m
    | TFun _ -> 8L
    | TDlg _ -> 8L
    | Tn -> -1L
    | _ -> raise(TypeError(3704, p, "size calculate error"))

(**
 * valの追加
 *)
let addVal(id: string):unit =
    envVals <- id :: envVals

let checkVal(id: string):bool =
    match List.tryFind (fun a -> a = id) envVals with
    | None ->
        if contains(id) then false
        else GlobalEnv.checkVal(id)
    | Some _ -> true

let checkVar(id: string):bool =
    match List.tryFind (fun a -> a = id) envVals with
    | None ->
        if contains(id) then true
        else GlobalEnv.checkVar(id)
    | Some _ -> false
