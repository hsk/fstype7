module TransClass

open AST
open Compact

(*
// 位置情報を構文木に付け加える
let p(t: Token, e: E): E =
    e.pos = t.pos
    e

// 位置情報を構文木に付け加える
let p(t: E, e: E): E =
    e.pos = t.pos
    e

// 位置情報をタイプに付け加える
let q(o: Token, t: T): T =
    t.pos = o.pos
    t

let splitDefs(b:Token, defs:(Token list * Token list)):(Token list * Token list) =
    match (b,defs) with
        // メソッドを発見
    | Bin(Pre((Id(_, "def") as o),Bin(Msg(Id(_, name),Id(_, "("),r,Id(_, ")")),Id(_, ":"),typ)),Id(_, "="),b),(d1,d2) ->
        ((name, r, typ, b)::d1, d2)
    | Pre((Id(_, "def") as o),Msg(Msg(Id(_, name),Id("("),r,Id(")")),(Id("{") as o2),e,Id("}"))), (d1, d2) ->
        ((name, r, Id("void"), (o2, e, Id("}")))::d1, d2)
    | Pre((Id(_, "def") as o),Bin(Msg(Id(name),Id("("),b,Id(")")),Id(":"),typ)), (d1, d2) ->
        ((name, b, typ, null)::d1, d2)
    | Pre(Id(_, "var"), b), (d1,d2) -> (d1, b::d2)
        // 全データを検索する
    | (Bin(x, (Id("@") as at), y), defs) -> splitDefs(x,splitDefs(y,defs))
    | _ -> raise(Exception(" b=" + b.ToString()))

(**
 * メソッド操作の変換
 * 
 * a->hoge()
 * を
 * a->classInfo->hoge(a)
 * に変換する
 *) 
let method(b: Any): Any = {
}


(**
 * ClassInfoが登録されていなかった場合は登録する
 * 
 * typedef ClassInfo = struct {
 *     parent:Ptr[ClassInfo]
 * }
 *)
let addClassInfo():unit =
    if (!global_env.map.contains("ClassInfo")) then
        GlobalEnv.addTypeDef("ClassInfo", TStruct(ListMap("parent"->Tp(TDef("ClassInfo")))))

let fprms(x:Any):Any =
    match x with
    | (a,Id(":"), b)->b
    | (a,Id(","), b)->(fprms(a),Id(","),fprms(b))
    

(**
 * 固有のclass用構造体を作成する
 * 
 * class A {
 *     var a:int
 *     def this(a:int) {}
 *     def setA(a:int) {...}
 *     def getA():int = {...}
 * }
 * // メンバ変数
 * typedef A = struct{
 *     classInfo:Ptr[A_ClassInfo]
 *     a:int
 * }
 * // メソッド
 * typedef A_ClassInfo = struct {
 *     parent:Ptr[ClassInfo]
 *     this:Ptr[(Ptr[A], int)=>Ptr[A]]
 *     setA:Ptr[(Ptr[A], int)=>void]
 *     getA:Ptr[(Ptr[A])=>int]
 * }
 *)
let transTypeDef(a: Id, id: String, vars:List[Any], defs:List[Any]): Any =
    let f(a:List[Any]):Any =
    match a with
    | List() -> Id("void")
    | List(a) -> a
    | a::b -> (a,Id("@"),f(b))

    let d(x:Any):Any =
        match x with
        | ("this", prms, Id("void"),body) -> // this:Ptr[(Ptr[A], int)=>Ptr[A]]
            let ptra = (Id("Ptr"),Id("["), a, Id("]"))
            let prms2 =
                match prms with
                | Id("void") -> ptra
                | _ -> (ptra, Id(","), fprms(prms))
            let fn = ( (Id("("), prms2 , Id(")"))    , Id("=>"), ptra)
            (Id("this"),Id(":"),(Id("Ptr"),Id("["),fn, Id("]")))
        | (name:String,prms,typ,body) ->
             // name:Ptr[(Ptr[A], prms)=>typ]
            let ptra = (Id("Ptr"),Id("["), a, Id("]"))
            let prms2 =
                match prms with
                | Id("void") -> ptra
                | _ -> (ptra, Id(","), fprms(prms))
            let fn = ( (Id("("), prms2 , Id(")"))    , Id("=>"), typ)
            (Id(name),Id(":"),(Id("Ptr"),Id("["),fn, Id("]")))

    // メソッドの型情報のみ取り出す
    let ds(a:Any):Any =
        match a with
        | List() -> Id("void")
        | List(a) -> d(a)
        | a::b -> (d(a),Id("@"),ds(b))
    let vars2 = ((Id("classInfo"),Id(":"),(Id("Ptr"),Id("["),Id(id+"_ClassInfo"),Id("]"))),Id("@"),f(vars))

    let tdef_vars = (Id("typedef"), (a, Id("="), (Id("struct"), Id("{"), vars2, Id("}"))))
    let classInfo = (Id("parent"),Id(":"),(Id("Ptr"),Id("["),Id("ClassInfo"),Id("]")))
    let tdef_defs = (Id("typedef"), (Id(id+"_ClassInfo"), Id("="), (Id("struct"), Id("{"), (classInfo ,Id("@"),ds(defs)), Id("}"))))
    (tdef_vars, Id("@"), tdef_defs)

(**
 * メソッドを変換する
 * def A_this(this:Ptr[A], a:int):Ptr[A] = { this->a = a; this}
 * def A_setA(this:Ptr[A], a:int):void = { this->a = a }
 * def A_getA(this:Ptr[A]):int = { this->a }
 * def A_hoge(this:Ptr[A]):int = { A_getA(this) }
 *)
let transDefs(a: Id, id: String, defs:List[Any]): Any =
    let d2 = defs.map
        | ("this", prms, typ, b) ->
            let ptra = (Id("this"), Id(":"), (Id("Ptr"), Id("["), a, Id("]")))
        // メソッドを通常の関数として定義する
            let prms2 =
                match prms with
                | Id("void") -> ptra
                | _ -> (ptra, Id(","), prms)
            
            ((Id("def"),
                ((Id(id + "_this"), Id("("), prms2, Id(")")), Id(":"), (Id("Ptr"), Id("["), a, Id("]")))), Id("="), (Id("{"), (b, Id("@"), Id("this")), Id("}")))
        | (fname, prms, typ, b) ->
            let ptra = (Id("this"), Id(":"), (Id("Ptr"), Id("["), a, Id("]")))
        // メソッドを通常の関数として定義する
            let prms2 =
                match prms with
                | Id("void") -> ptra
                | _ -> (ptra, Id(","), prms)
            
            ((Id("def"),
                ((Id(id + "_" + fname), Id("("), prms2, Id(")")), Id(":"), typ)), Id("="), (Id("{"), b, Id("}")))
        | e -> throw new Exception("e="+e)
    d2.foldLeft(null:Any){case (null,a)-> a case(b,c)->(b,Id("@"),c)}

(**
 * class_infoの実体を作る
 * 
 * var __A_classInfo__:A_ClassInfo = ( 0, A_this, A_setA, A_getA, A_hoge )
 * 
 *)
let transInstanceClassInfo(a: Id, id: String, defs:List[Any]): Any =
    let tpl = defs.foldLeft(Lng(0):Any) {case (a:Any,(name:String,prms,t,b)) -> (a, Id(","), Id(id+"_"+name) ) }
    let tpl2 = (Id("("),tpl,Id(")"))
    ((Id("var"), (Id("__"+id+"_ClassInfo__"),Id(":"),Id(id+"_ClassInfo"))),Id("="),tpl2)

(**
 * アロケータを作成する
 * def A_alloc():Ptr[A] = {
 *     var this:Ptr[A]
 *     this = new A
 *     this->classInfo = &a_classInfo
 *     this
 * }
 *)
let transAlloc(a: Id, id: String, b: Any): Any =
    let ptra = (Id("Ptr"),Id("["),a,Id("]"))
    let bs = [
        (Id("var"), (Id("this"), Id(":"), ptra));
        (Id("this"), Id("="), (Id("new"), a));
        ((Id("this"),Id("->"),Id("classInfo")), Id("="), (Id("&"),Id("__"+id+"_ClassInfo__")));
        Id("this");
    ]
    let bs2 = bs.foldLeft(null:Any){case (null,a)-> a case(b,c)->(b,Id("@"),c)}
    let body = (Id("{"), bs2, Id("}"))
    ((Id("def"),((Id(id+"_alloc"),Id("("),Id("void"),Id(")")),Id(":"),ptra)),Id("="),body)


(**
 * クラスの変換
 *)
let klass(a: Token, b: Token): Token =
    // 親クラスInfoを読み込む
    addClassInfo()

    let id: string =
        match a with
        | Id(_,a) -> a
        | _ -> raise(TypeError(8000, a.p, "error"))

    let (defs1, vars1) = splitDefs(b, ([], []))
    let (vars,defs) = (vars1.reverse, defs1.reverse)
    // 構造体を作成する
    let typeDef = transTypeDef(a, id, vars, defs)
    // メソッドを変換する
    let defs2 = transDefs(a, id, defs)
    // classInfo構造体の実体を作る
    let instanceClassInfo = transInstanceClassInfo(a, id, defs)
    // アロケータを作成する
    let alloc = transAlloc(a, id, b)
    // 結合して返却する
//        (typeDef, Id("@"), (defs2, Id("@"), (instanceClassInfo, Id("@"), alloc)))
//        throw new Exception("defs2 = "+defs2)
//        ((Id(def),((Id(A_this),Id((),((Id(this),Id(:),(Id(Ptr),Id([),Id(A),Id(]))),Id(,),(Id(a),Id(:),Id(int))),Id())),Id(:),(Id(Ptr),Id([),Id(A),Id(])))),Id(=),(Id({),(((Id(this),Id(->),Id(a)),Id(=),Id(a)),Id(@),Id(this)),Id(})))
    let rc = (((typeDef, Id("@"), defs2), Id("@"), instanceClassInfo), Id("@"), alloc)
//        let rc = ((typeDef, Id("@"), defs2), Id("@"), instanceClassInfo)
    println("typeDef "+typeDef)
    println("defs2 "+defs2)
    println("instanceClassInfo "+instanceClassInfo)
    println("alloc "+alloc)
    //throw new Exception("rc "+rc)
    rc

let rec f(st: Token): Token =
    match st with
    | Pre(Id(_, "typedef") as o, Bin(Id(_,_) as a, Id(_, "="), Msg(Id(_, "class"), Id(_, "{"), b, Id(_, "}")))) -> klass(a, b)
    | Bin(a, (Id(_, "@") as id), b) -> Bin(f(a), id, f(b))
    | o -> o


let apply(st: Token): Token =
    f(st)
*)