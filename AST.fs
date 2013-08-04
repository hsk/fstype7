module AST

open System

(**
 * 型
 *)
type T =
    (** 符号付き整数型 *)
    | Ti of int
    (** 符号無し整数型 *)
    | Tu of int
    (** 単精度浮動小数点数 *)
    | Tf
    (** 倍精度浮動小数点数 *)
    | Td
    (** 型未定義 *)
    | Tn
    (** void型 *)
    | Tv
    (** リターン値型 *)
    | Tr of T
    (** ポインタ型 *)
    | Tp of T
    (** 配列型 *)
    | TArr of T * int64
    (** 構造体型 *)
    | TStr of (string * T) list
    (** 型定義 *)
    | TDef of string
    (** 関数型 *)
    | TFun of T * T list

type P(src:string, no:int) =
    member this.no
        with get() = no
    override this.ToString():string = this.p()
    
    member this.p():string =
        let rec getLineNo(start:int, line:int):string =
            let index = src.IndexOf('\n', start)
            if (index < 0) then
                "EOF"
            else if (index >= this.no) then
                "(" + line.ToString() + ")"
            else
                getLineNo(index+1, line + 1)
        getLineNo(0, 1)

let P0 = P("", 0)


(**
 * 抽象構文木
 *)
type E =
    (** 変数定義 *)
    | EVar of P * T * string * E
    (** 不変変数定義 *)
    | EVal of P * T * string * E
    (** ブロック構文 *)
    | EBlock of P * T * E list
    (** 整数定数ロード *)
    | ELd of P * T * int64
    (** 浮動小数点数定数ロード *)
    | ELdd of P * T * double
    (** 文字列定数ロード *)
    | ELds of P * T * string
    (** 変数の参照 *)
    | EId of P * T * string
    (** 配列 *)
    | EArray of P * T * E * E
    (** 二項演算子 *)
    | EBin of P * T * T * string * E * E
    (** -単項演算子 *)
    | ENeg of P * T * E
    (** !演算子 *)
    | ENot of P * T * E
    (** 代入 *)
    | EAssign of P * T * E * E
    (** 配列割り当て *)
    | ENewArray of P * T * E
    (** ヒープから割り当て *)
    | ENew of P * T
    (** GC付きの変数の割り当て *)
    | EGCNew of P * T
    (** ポインタ値取得 *)
    | ERef of P * T * E
    (** ポインタ値参照 *)
    | EPtr of P * T * E
    (** 構造体のフィールド参照 *)
    | EField of P * T * T * E * string
    (** アロー演算子 *)
    | EArrow of P * T * T * E * string
    (** 型定義 *)
    | ETypeDef of P * T * string
    (** コメント *)
    | ENop of P * T * string
    (** 関数呼び出し *)
    | ECall of P * T * E * E list
    (** 関数 *)
    | EFun of P * T * string * (string * T) list * E
    (** if 式 *)
    | EIf of P * T * E * E * E
    (** while 文 *)
    | EWhile of P * T * E * E
    (** do while 文 *)
    | EDo of P * T * E list * E
    (** for文 *)
    | EFor of P * T * E * E * E * E
    (** switch文 *)
    | ESwitch of P * T * E * (E * E) list
    (** ジャンプ *)
    | EGoto of P * T * string
    (** ラベル *)
    | ELabel of P * T * string * E
    (** break *)
    | EBreak of P * T
    (** continue *)
    | EContinue of P * T
    (** ケース *)
    | ECase of P * T * E * E
    (** サイズ取得 *)
    | ESizeOf of P * T * T * E
    (** リターン *)
    | ERet of P * T * E
    (** キャスト *)
    | ECast of P * T * E
    (** 多値 *)
    | ETuple of P * T * E list
    (** 多値 *)
    | EImport of P * string
    | ENull of P
(**
 * 二項演算子の構築用
 *)
let EOp(op: String)(p:P, t: T, a: E, b: E): E =
    EBin(p, t, t, op, a, b)

(**
 * 比較演算子の構築
 *)
let EOpc(op: String)(p:P, t: T, a: E, b: E): E =
    EBin(p, Ti(64), t, op, a, b)

(** 加算 *)
let EAdd:(P * T * E * E) -> E = EOp("add")
(** 減算算 *)
let ESub:(P * T * E * E) -> E = EOp("sub")
(** 乗算 *)
let EMul:(P * T * E * E) -> E = EOp("mul")
(** 割算 *)
let EDiv:(P * T * E * E) -> E = EOp("div")
(** 剰余 *)
let EMod:(P * T * E * E) -> E = EOp("mod")
(** 左シフト *)
let EShl:(P * T * E * E) -> E = EOp("shl")
(** 算術右シフト *)
let EShr:(P * T * E * E) -> E = EOp("shr")
(** 右シフト *)
let EUshr:(P * T * E * E) -> E = EOp("ushr")
(** 論理積 *)
let EAnd:(P * T * E * E) -> E = EOp("and")
(** 論理和 *)
let EOr:(P * T * E * E) -> E = EOp("or")
(** 排他的論理和 *)
let EXor:(P * T * E * E) -> E = EOp("xor")
(** <=比較演算子 *)
let EGe:(P * T * E * E) -> E = EOpc("ge")
(** <比較演算子 *)
let EGt:(P * T * E * E) -> E = EOpc("gt")
(** &lt;=比較演算子 *)
let ELe:(P * T * E * E) -> E = EOpc("le")
(** >比較演算子 *)
let ELt:(P * T * E * E) -> E = EOpc("lt")
(** `==`比較演算子 *)
let EEq:(P * T * E * E) -> E = EOpc("eq")
(** !=比較演算子 *)
let ENe:(P * T * E * E) -> E = EOpc("ne")


(**
 * 抽象構文木のルート
 *)
type Prog =
    | Prog of E list

type R =
    | RG of T * string
    | RL of T * string
    | RR of T * string
    | RN of T * string
    | RNULL

(**
 * LLVM命令
 *)
type LL =
    (** 関数コール *)
    | LLCall of R * R * R list
    (** 二項演算子 *)
    | LLBin of R * string * R * R
    (** 単項演算子 *)
    | LLUnary of R * string * R
    (** 代入演算子疑似命令 *)
    | LLAssign of R * R
    (** 値読込 *)
    | LLLoad of R * R
    (** 値設定 *)
    | LLStore of R * R
    (** スタック上のメモリ確保 *)
    | LLAlloca of R
    (**
     * キャスト全般疑似命令
     * 
     * LLVMのキャストは色々あるのだけど、１つに纏めてあります。
     *)
    | LLCast of R * R
    (** フィールドアクセス疑似命令 *)
    | LLField of R * R * R * R
    (** 関数 *)
    | LLFun of T * string * (string *T) list * (string * T) list * LL list * R

    (** コメント *)
    | LLNop of string
    (** 条件分岐 *)
    | LLJne of R * string * string * string
    (** ジャンプ命令 *)
    | LLGoto of string * string
    (** ラベル命令 *)
    | LLLabel of string * string
    (** SSA最適化のφ(ファイ) 複数基本ブロックの変数を１つに合流させる *)
    | LLPhi of R * string * string * T * R * R
    (** テーブルジャンプ命令 *)
    | LLSwitch of R * string * (R * string) list
    (** グローバル変数 *)
    | LLGlobal of R * R
    (** 文字列疑似命令　ローカルに書けるような感じにしてありますが、emitで、関数の外に文字列定数を出力し参照します。 *)
    | LLLoadCStr of R * string

module GenId =
    let mutable id = 0
    let genid(s: string): string =
        id <- id + 1
        sprintf "%s%d" s id

type R with
    member this.t =
        match this with
        | RG(t,id) -> t
        | RL(t,id) -> t
        | RR(t,id) -> t
        | RN(t,id) -> t
        | RNULL -> Tv
    member this.id =
        match this with
        | RG(t,id) -> id
        | RL(t,id) -> id
        | RR(t,id) -> id
        | RN(t,id) -> id
        | RNULL -> ""

    (**
     * 変数をLLVM用に出力
     *)
    member this.p =
        match this with
        | RG(t,id) -> "@" + id
        | RL(t,id) -> "%" + id
        | RR(t,id) -> "%." + id
        | RN(Tf, id) ->
            let f = Convert.ToSingle(id)
            let d = Convert.ToDouble(f)
            let l = BitConverter.DoubleToInt64Bits(d)
            sprintf "0x%x" l
        | RN(Td, id) ->
            let d = Convert.ToDouble(id)
            let l = BitConverter.DoubleToInt64Bits(d)
            sprintf "0x%x" l
        | RN(t,id) -> "" + id
        | RNULL -> "null"
    
    (**
     * RにTを設定
     *
     * @param a: R レジスタ
     * @param t: T 型
     * @return R 返り値レジスタ
     *)
    member this.setT(t: T): R =
        match this with
        | RL(_,id) -> RL(t,id)
        | RG(_,id) -> RG(t,id)
        | RR(_,id) -> RR(t,id)
        | RN(_,id) -> RN(t,id)
        | RNULL -> RNULL

(** 構造体のレジスタ名へのmap *)
let mutable structs:(T * R) list = []

(** 環境 *)
let mutable envmap:(string * T) list = []

(** グローバルなシンボルテーブル *)
let mutable globalmap:(string * T) list = []

type T with
    static member structsfind(t:T):R =
        let (a, b) = List.find (function | (id1, _) -> id1 = t) structs
        b
    static member add(a:T*R):unit =
        let rec add(a:T*R) =
            match a with
            | (TStr(ls) as t,_) ->
                match (List.tryFind (fun (t1,r) -> t=t1) structs) with
                | None ->
                    structs <- a :: structs
                    List.iter (fun (id,t) -> add(t , RL(t, GenId.genid(".struct")))) ls
                | _ -> ()
            | (TDef(id) as t,_) -> add((t, RL(T.find(id), GenId.genid(".struct"))))
            | _ -> ()
        add(a)
    static member structs = structs
    static member find(id:string):T =
        try
            envmap |> List.find (fun(id2, t) -> id = id2) |> fun (a,b) -> b
        with
        | e ->
            globalmap |> List.find (fun(id2, t) -> id = id2) |> fun (a,b) -> b
        
    (**
     * ソースコード上の表現で型を文字列化します
     *)
    member this.ttos: string =
        match this with
        | Ti(8)-> "byte"
        | Ti(16)-> "short"
        | Ti(32)-> "int"
        | Ti(64)-> "long"
        | Tu(8)-> "ubyte"
        | Tu(16)-> "ushort"
        | Tu(32)-> "uint"
        | Tu(64)-> "ulong"
        | Tf-> "float"
        | Td-> "double"
        | Tn-> "void"
        | Tv-> "void"
        | Tr(t: T)-> "Ref[" + t.ttos + "]"
        | Tp(t: T)-> "Ptr[" + t.ttos + "]"
        | TArr(t: T, size)-> "Array[" + t.ttos + "," + size.ToString() + "]"
        | TStr(members: (string * T) list)->
            let f a b = 
                match b with
                | (s, t:T) -> a + " " + s + ":" + t.ttos
            "struct{" + (List.fold f "" members) + " }"
        | TDef(id: String)-> id
        | TFun(t, prms)->
            "(" + System.String.Join(", ", List.map (fun (t:T) -> t.ttos) prms) + ")->" + t.ttos
        | _-> raise (Exception("error type " + this.tName))

    (**
     * 1文字表現で型を文字列化します
     *)
    member this.tName:string =
        match this with
        | Ti(8)-> "b"
        | Ti(16)-> "s"
        | Ti(32)-> "i"
        | Ti(64)-> "l"
        | Tu(8)-> "c"
        | Tu(16)-> "w"
        | Tu(32)-> "u"
        | Tu(64)-> "q"
        | Tf-> "f"
        | Td-> "d"
        | TDef(id)-> T.find(id).tName
        | TArr _ -> "p"
        | TStr _ -> "p"
        | TFun _ -> "p"
        | Tp _ -> "a"
        | Tr _ -> "a"
        | _-> raise(Exception("a " + this.ttos))
    (**
     * 型のTDefを消し、生のデータを返します。
     * 
     * ただし、再帰的な型名があった場合はそのままの型名で返却します。
     * さもないと、無限ループしてしまいます。
     *)
    member this.stripType(set:string list):T =
        match this with
        | TDef(id) ->
            if (set |> List.tryFindIndex (fun i -> i=id)) <> None then this
            else
                try
                    T.find(id).stripType(id :: set)
                with
                | _ -> raise(Exception ("not found typename "+id))
        | TStr(m) -> TStr(List.map (fun (id,t:T)->(id, t.stripType(set))) m)
        | TArr(t1, size) -> TArr(t1.stripType(set), size)
        | Tp(t1) -> Tp(t1.stripType(set))
        | _ -> this
    (**
     * 型をLLVM用に出力
     *)
    member this.p:string =
        match this with
        | Tn -> "i8"
        | Ti(i) -> sprintf "i%d" i
        | Tu(i) -> sprintf "i%d" i
        | Tf -> "float"
        | Td -> "double"
        | Tv -> "void"
        | TFun(t1, ls) ->
            let f (a:T):string = a.p
            t1.p + "(" + System.String.Join(", ", List.map f ls) + ")*"
        | TArr(t, size) -> sprintf "[%d x %s]" size (t.p)
        | Tr(t) -> t.p
        | Tp(t) -> t.p + "*"
        | TDef _ -> this.stripType([]).p
        | TStr ls ->
            match (List.tryFind (fun (t,r) -> t=this) structs) with
            | None ->
                let id = GenId.genid(".struct")
                structs <- (this , RL(this, id)) :: structs
                List.iter (fun (id,t:T) -> t.p |> ignore) ls
            | _ -> ()
            let r = T.structsfind(this)
            r.p
    (**
     * 配列はポインタに変換して型を文字列として出力します。
     *)
    member this.p2: string =
        let rec f(t: T): T =
            match t with
            | TArr(t, s) -> Tp(f(t))
            | TDef(s) -> f(T.find(s))
            | t -> t
        f(this).p

(**
 * プリント関数の呼び出し
 *)
let EPrint (p:P, t:T, e:E):E =
    ECall(p, Tv, EId(p, TFun(Tv, [t]),"print_"+t.tName), [e])

type E with
    member this.pos =
        match this with
        | _ -> P0
    member this.t =
        match this with
        | EVar(p,_,_,_) -> Tv
        | EVal(p,_,_,_) -> Tv
        | EBlock(p,t,_) -> t
        | ELd(p,t,_) -> t
        | ELdd(p,t,_) -> t
        | ELds(p,t,_) -> t
        | EId(p,t,_) -> t
        | EArray(p,t,_,_) -> t
        | EBin(p,t,_,_,_,_) -> t
        | ENeg(p,t,_) -> t
        | ENot(p,t,_) -> t
        | EAssign(p,t,_,_) -> t
        | ENewArray(p,t,_) -> t
        | ENew(p,t) -> t
        | EGCNew(p,t) -> t
        | ERef(p,t,_) -> t
        | EPtr(p,t,_) -> t
        | EField(p,t,_,_,_) -> t
        | EArrow(p,t,_,_,_) -> t
        | ETypeDef(p,t,_) -> Tv
        | ENop(p,t,_) -> t
        | ECall(p,t,_,_) -> t
        | EFun(p,t,_,_,_) -> t
        | EIf(p,t,_,_,_) -> t
        | EWhile(p,t,_,_) -> t
        | EDo(p,t,_,_) -> t
        | EFor(p,t,_,_,_,_) -> t
        | ESwitch(p,t,_,_) -> t
        | EGoto(p,t,_) -> t
        | ELabel(p,t,_,_) -> t
        | EBreak(p,t) -> t
        | EContinue(p,t) -> t
        | ECase(p,t,_,_) -> t
        | ESizeOf(p,t,_,_) -> t
        | ERet(p,t,_) -> t
        | ECast(p,t,_) -> t
        | ETuple(p,t,_) -> t
        | EImport(p,_) -> Tv
        | ENull(p) -> Tv
        
    member this.setT(t:T):E =
        match this with
        | EVar(p,_,a,b) -> EVar(p,t,a,b)
        | EVal(p,_,a,b) -> EVal(p,t,a,b)
        | EBlock(p,_,a) -> EBlock(p,t,a)
        | ELd(p,_,a) -> ELd(p,t,a)
        | ELdd(p,_,a) -> ELdd(p,t,a)
        | ELds(p,_,a) -> ELds(p,t,a)
        | EId(p,_,a) -> EId(p,t,a)
        | EArray(p,_,a,b) -> EArray(p,t,a,b)  
        | EBin(p,_,a,b,c,d) -> EBin(p,t,a,b,c,d)
        | ENeg(p,_,a) -> ENeg(p,t,a)
        | ENot(p,_,a) -> ENot(p,t,a)
        | EAssign(p,_,a,b) -> EAssign(p,t,a,b)
        | ENewArray(p,_,a) -> ENewArray(p,t,a)
        | ENew(p,_) -> ENew(p,t) 
        | EGCNew(p,_) -> EGCNew(p,t)
        | ERef(p,_,a) -> ERef(p,t,a)
        | EPtr(p,_,a) -> EPtr(p,t,a)
        | EField(p,_,a,b,c) -> EField(p,t,a,b,c)
        | EArrow(p,_,a,b,c) -> EArrow(p,t,a,b,c)
        | ETypeDef(p,_,a) -> ETypeDef(p,t,a)
        | ENop(p,_,a) -> ENop(p,t,a)
        | ECall(p,_,a,b) -> ECall(p,t,a,b)
        | EFun(p,_,a,b,c) -> EFun(p,t,a,b,c)
        | EIf(p,_,a,b,c) -> EIf(p,t,a,b,c)
        | EWhile(p,_,a,b) -> EWhile(p,t,a,b)
        | EDo(p,_,a,b) -> EDo(p,t,a,b)
        | EFor(p,_,a,b,c,d) -> EFor(p,t,a,b,c,d)
        | ESwitch(p,_,a,b) -> ESwitch(p,t,a,b)
        | EGoto(p,_,a) -> EGoto(p,t,a)
        | ELabel(p,_,a,b) -> ELabel(p,t,a,b)
        | EBreak(p,_) -> EBreak(p,t)
        | EContinue(p,_) -> EContinue(p,t)
        | ECase(p,_,a,b) -> ECase(p,t,a,b)
        | ESizeOf(p,_,a,b) -> ESizeOf(p,t,a,b)
        | ERet(p,_,a) -> ERet(p,t,a)
        | ECast(p,_,a) -> ECast(p,t,a)
        | ETuple(p,_,a) -> ETuple(p,t,a)
        | EImport(p,a) -> this
        | ENull(p) -> this
