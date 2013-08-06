(**
 * グローバルな環境
 *)
module GlobalEnv

open AST

let mutable ts = new Map<T, string>([])

(**
 * 初期化
 *)
let init() =
    globalmap <- [
      "println", TFun(Tv,[Tp(Tu(8))]);
      "print_b", TFun(Tv,[Ti(8)]);
      "print_s", TFun(Tv,[Ti(16)]);
      "print_i", TFun(Tv,[Ti(32)]);
      "print_l", TFun(Tv,[Ti(64)]);
      "print_f", TFun(Tv,[Tf]);
      "print_d", TFun(Tv,[Td]);
      "char", Tu(8);
      "byte", Ti(8);
      "short", Ti(16);
      "int", Ti(32);
      "long", Ti(64);
      "double", Td;
      "float", Tf
    ]
    structs <- []
    ()

init() |> ignore

(**
 * シンボルを追加
 *)
let add(id: string, t: T):unit =
    globalmap <- (id, t) :: globalmap

(**
 * 型の追加
 *)
let addTypeDef(id: string, t: T):unit = 
    globalmap <- (id, t) :: globalmap
    t.p |> ignore

(**
 * シンボルを検索
 *)
let mapfind(id:string):T =
    try
        globalmap |> List.find (fun(id2, t) -> id = id2) |> fun(a,b) -> b
    with
    | e ->
        printfn "global %A env %A " globalmap envmap
        raise (TypeError(3601, P0, sprintf "%s not found." id))
(**
 * シンボル検索
 *)
let contains(id:string):bool =
    try
        globalmap |> List.find (fun(id2, t:T) -> id = id2) |> ignore
        true
    with
        e -> false
