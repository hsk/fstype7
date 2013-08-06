module Alpha

open AST
open System

let mutable genv = new Map<string, string>([])

let find(id: string, env: Map<string, string>): string = 
    match env.TryFind(id) with
    | Some(v) -> v
    | None -> id


let add(env:Map<string, string>, a:(string * string)):Map<string,string> =
    genv <- genv.Add(a)
    env.Add(a)

let rec f(e: E, env: Map<string, string>): E * Map<string, string> = 
    let rec l(ls: E list, env: Map<string, string>): (E list * Map<string, string>) =
        let ff (ls:E list, env:Map<string, string>) a =
            let (a1, env1) = f(a, env)
            ((a1 :: ls), env1)
        let (ls2, env2) = List.fold ff ([], env) ls
        (ls2 |> List.rev, env2)

    let rec l2(ls: (E * E) list, env: Map<string, string>): (E * E) list * Map<string, string> = 
        let ff (ls, env) (a, b) =
            let (a1, env1) = f(a, env)
            let (b1, env2) = f(b, env1)
            (((a1, b1) :: ls), env)
        let (cases1, env2) = List.fold ff  ([], env) ls
        (cases1 |> List.rev, env2)

    let rc =
        match e with
        | EBin(p, t: T, t2: T, i: string, a: E, b: E) ->
            let (a1, env1) = f(a, env)
            let (b1, env2) = f(b, env1)
            (EBin(p, t, t2, i, a1, b1), env2)
        | ELd(p, t: T, i: int64) -> (ELd(p, t, i), env)
        | EBlock(p, t: T, ls: E list) ->
            let (ls1, env1) = l(ls, env)
            (EBlock(p, t, ls1), env)
        | ECall(p, t: T, a: E, b) ->
            let (b1, env1) = l(b, env)
            let (a1, env2) = f(a, env1)
            (ECall(p, t, a1, b1), env2)
        | EVar(p, t: T, id: String, a) ->
            let (a1, env1) =
                match a with
                | ENull(_) -> (a, env)
                | _ -> f(a, env)
            let id2 = if (genv.ContainsKey(id)) then GenId.genid(".") else id
            (EVar(p, t, id2, a1), add(env1, (id,id2)))
        | EVal(p, t: T, id: String, a) ->
            let (a1, env1) =
                match a with
                | ENull(_) -> (a, env)
                | _ -> f(a, env)
            let id2 = if (genv.ContainsKey(id)) then GenId.genid(".") else id
            (EVal(p, t, id2, a1), add(env1,(id,id2)))
        | EId(p, t: T, id: string) -> (EId(p, t, find(id, env)), env)
        | EField(p, t: T, t2: T, id: E, idx: string) ->
            let (id1, env1) = f(id, env)
            (EField(p, t, t2, id1, idx), env)
        | EAssign(p, t: T, a: E, b: E) ->
            let (a1, env1) = f(a, env)
            let (b1, env2) = f(b, env1)
            (EAssign(p, t, a1, b1), env2)
        | ESwitch(p, t: T, a: E, cases: (E * E) list) ->
            let (a1, env1) = f(a, env)
            let (cases1, _) = l2(cases, env1)
            (ESwitch(p, t, a1, cases1), env)
        | ENop _ -> (e, env)
        (*
        | ETag(t: T, id:String, ls: List[E]) ->
            let (ls1, env1) = l(ls, env)
            (p(e, ETag(t, id, ls1)), env1)*)
        | ETuple(p, t: T, ls: E list) ->
            let (ls1, env1) = l(ls, env)
            (ETuple(p, t, ls1), env1)
        | ETypeDef(p, t: T, id: string) -> (ETypeDef(p, t, id), env)
        | EArray(p, t, a, b) ->
            let (a1, env1) = f(a, env)
            let (b1, env2) = f(b, env1)
            (EArray(p,t,a1,b1), env)
        | EArrow(p, t, t2, a, b) ->
            let (a1, env1) = f(a, env)
            (EArrow(p,t,t2, a1, b), env)
        
        | EBreak(p,_) -> (e, env)
        | ECase(p,t, a, b) ->
            let (a1, env1) = f(a, env)
            let (b1, env2) = f(b, env1)
            (ECase(p,t,a1,b1), env)
        | ECast(p,t, a) ->
            let (a1, env1) = f(a, env)
            (ECast(p,t,a1), env1)
        | EContinue(p,_) -> (e, env)
        | EDo(p,t, ls, a) ->
            let (ls1, env1) = l(ls, env)
            let (a1, env2) = f(a, env1)
            (EDo(p, t, ls1, a1), env)
        | EFor(p, t, a, b, c, d) ->
            let (a1,env1) = f(a,env)
            let (b1,env2) = f(b,env1)
            let (c1,env3) = f(c,env2)
            let (d1,env4) = f(d,env3)
            (EFor(p,t,a1,b1,c1,d1), env)
        | EFun(p, t, a, b, c) ->
            let (c1,env1) = f(c,env)
            (EFun(p,t,a,b,c1), env)
        | EGCNew(p,_) -> (e, env)
        | EGoto(p,_, _) -> (e, env)
        | EIf(p,t, a, b, c) ->
            let (a1,env1) = f(a,env)
            let (b1,env2) = f(b,env1)
            let (c1,env3) = f(c,env1)
            (EIf(p,t,a1,b1,c1), env)
        
        | EImport(p,_) -> (e, env)
        | ELabel(p,t, i, a) ->
            let (a1,env1) = f(a,env)
            (ELabel(p,t,i,a1), env)
        | ELdd(p,_, _) -> (e, env)
        | ELds(p,_, _) -> (e, env)
        | ENeg(p, t, a) ->
            let (a1,env1) = f(a,env)
            (ENeg(p,t,a1), env)
        
        | ENew(p,_) -> (e, env)
        | ENewArray(p,t, a) ->
            let (a1,env1) = f(a,env)
            (ENewArray(p,t,a1), env)
        | ENot(p,t,a) ->
            let (a1,env1) = f(a,env)
            (ENot(p,t,a1), env)
        | EPtr(p,t,a) ->
            let (a1,env1) = f(a,env)
            (EPtr(p,t,a1), env)
        | ERef(p,t, a) ->
            let (a1,env1) = f(a,env)
            (ERef(p,t,a1), env)
        | ERet(p,t, a) ->
            let (a1,env1) = f(a,env)
            (ERet(p,t,a1), env)
        | ESizeOf(p,t, t1, a) ->
            let (a1,env1) = f(a,env)
            (ESizeOf(p,t,t1,a1), env)
        | EWhile(p,t, a, b) ->
            let (a1,env1) = f(a,env)
            let (b1,env2) = f(b,env1)
            (EWhile(p,t,a1,b1), env)
        
        | ENull(p) -> (e, env)
    // Console.Write(e.ToString()+"->"+rc.ToString())
    rc

let g(e: E): E =
    genv <- new Map<string, string>([])
    match f(e, new Map<string, string>([])) with
    | (e, _) -> e

let apply(prog:Prog):Prog =
    match prog with
    | Prog(b) -> Prog(b |> List.map (fun(e:E) -> g(e)))
