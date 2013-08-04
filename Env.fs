(**
 * 環境
 *)
module Env

open AST
open System

(** ファイル名 *)
let mutable filename = ""

(**
 * 環境のコピー
 *)
let copy(): (string *T) list = envmap

(**
 * 環境の読み込み
 *)
let load(e: (string *T) list):unit = envmap <- e

(**
 * 環境の初期化
 *)
let init(p: (string *T) list):unit = load(p)

(**
 * シンボル検索
 *)
let find(id:string):T =
    try
        let (_, b) = List.find (function | (id2, t) -> id = id2) envmap
        b
    with
        e ->
            GlobalEnv.mapfind(id)

(**
 * シンボル検索
 *)
let contains(id:string):bool =
    try
        List.find (function | (id2, t) -> id = id2) envmap |> ignore
        true
    with
        e -> false

let mapfind(id:string):T = find id

(**
 * 検索してレジスタで返却
 *)
let findR(id: string):R =
//    printfn "%A" envmap
    if contains(id) then
        RL(find(id),id)
    else
        try
            RG(GlobalEnv.mapfind(id),id)
        with
        | e -> raise(Exception("not found "+id))

(**
 * 型定義追加
 *)
let addTypeDef(id: string, t: T):unit =
    envmap <- (id, t) :: envmap
let getFieldNo(id: string, field: string):int =
    match mapfind(id) with
    | TStr(m) ->
        let rec getNo(no:int, m:(string * T) list):int =
            match m with
            | [] -> raise (Exception ("not found " + field))
            | (name,t)::xs when (name = field) -> no
            | x::xs -> getNo(no + 1, xs)
        getNo(0, m)
    | _ -> raise(Exception("error"))

(**
 * 型の追加
 *)
let add(id: string, t: T):unit =
    envmap <- (id, t) :: envmap
    t.p |> ignore

(**
 * サイズ計算
 *)
let rec size(t: T): int64 =
    match t with
    | Ti(i) -> (int64 i) / 8L
    | Tu(i) -> (int64 i) / 8L
    | Tf -> 4L
    | Td -> 8L
    | Tp(_) -> 8L
    | TDef(id) -> size(find(id)) 
    | TArr(t, s) -> size(t) * s
    | TStr(m) -> List.fold (fun a (t, b) -> a + size(b)) 0L m
    | TFun _ -> 8L
    | Tn -> -1L
    | _ -> raise(Exception "error")
