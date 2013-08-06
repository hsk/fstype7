module Regexp

open System.Text.RegularExpressions

type state =
| Char of char * state ref
| Split of state ref * state ref
| Match

type frag = {nfa: state; danglings: state ref list}


module PostOfRegEx =

    let mutable str = ""

    let (|Reg|_|) (regex:string) str =
        let m = Regex.Match(str, regex)
        if m.Success then
            Some ([ for x in m.Groups -> x.Value ])
        else None
    (**
     * regexp to post fix 
     *)
    let post_of_regex(regex:string):string =

        str <- regex
        let eat (regex:string):string =
            match str with
            | Reg regex [o] -> str.Substring(o.Length)
            | _ -> raise(System.Exception(sprintf "expected is %s but found %s" regex (str.Substring(0,1))))
        let rec expr():string =
            conc() + expr_tail()
        and expr_tail():string =
            match str with
            | Reg "^\\|" _ -> str <- str.Substring(1); conc () + "|" + expr_tail ()
            | _ -> ""
        and conc ():string =
            rept() + conc_tail()
        and conc_tail():string =
            match str with
            | "" | Reg "^([^\\(\\)a-z]|\\))" _ -> ""
            | _ -> rept() + "." + conc_tail()
        and rept():string =
            atom() + rept_tail()
        and rept_tail():string =
            match str with
            | Reg "^\\?" _ -> str <- str.Substring(1); "?"
            | Reg "^\\*" _ -> str <- str.Substring(1); "*"
            | Reg "^\\+" _ -> str <- str.Substring(1); "+"
            | _ -> ""
        and atom():string =
            match str with
            | Reg "^\\(" _ ->
                str <- str.Substring(1)
                let e = expr()
                str <- eat("^\\)")
                e
            | Reg "^[a-z]" [c] ->
                str <- str.Substring(1)
                c
            | _ -> raise(System.Exception ("error "+str))
        expr()

module NfaOfPost =

    let patch (l:state ref list)(s:state):unit =
        List.iter (fun (o:state ref) -> o := s) l

    let rec nfa_of_post2 (frags:frag list) (strm:string) =
        
        if strm.Length = 0
        then (List.head frags).nfa
        else
            match (strm.[0],frags) with
            | ('.', e2::e1::rest) ->
                let frags = {nfa = e1.nfa; danglings = e2.danglings}::rest
                patch (e1.danglings) e2.nfa
                nfa_of_post2 frags (strm.Substring(1))
            | ('|', e2::e1::rest) ->
                let out1 = ref e1.nfa
                let out2 = ref e2.nfa
                let nfa = Split (out1, out2)
                let danglings = e1.danglings @ e2.danglings
                nfa_of_post2 ({nfa = nfa; danglings = danglings}::rest) (strm.Substring(1))
            | ('?', e::rest) ->
                let out1 = ref e.nfa
                let out2 = ref Match
                let nfa = Split (out1, out2)
                nfa_of_post2 ({nfa = nfa; danglings = out2 :: e.danglings}::rest) (strm.Substring(1))
            | ('*', e::rest) ->
                let out1 = ref e.nfa
                let out2 = ref Match
                let nfa = Split (out1, out2)
                let frags = {nfa = nfa; danglings = [out2]}::rest
                patch (e.danglings) nfa
                nfa_of_post2 frags (strm.Substring(1))
            | ('+', e::rest) ->
                let out1 = ref e.nfa
                let out2 = ref Match
                let nfa = Split (out1, out2)
                let frags = {nfa = e.nfa; danglings = [out2]}::rest
                patch (e.danglings) nfa
                nfa_of_post2 frags (strm.Substring(1))
            | (c, frags) ->
                let out = ref Match
                let nfa = Char (strm.[0], out)
                nfa_of_post2 ({nfa = nfa; danglings = [out]}::frags) (strm.Substring(1))

    let nfa_of_post post =
        nfa_of_post2 [] post

let post_of_regex(regex:string):string = PostOfRegEx.post_of_regex(regex)
let nfa_of_post post = NfaOfPost.nfa_of_post(post)

let rec add_state state states =
    match List.tryFind (fun a -> a=state) states with
    | Some _ -> states
    | None ->
        match state with
        | Split (out1, out2) -> add_state !out1 (add_state !out2 states)
        | _ -> state::states


let step c states =
  let rec filter acc = function
      | Char (c2, out) -> if c = c2 then (add_state !out acc) else acc
      | _ -> acc
  List.fold filter [] states

let rec matching states strm = 
    match strm with
    | c::strm -> matching (step c states) strm
    | [] -> states

let match_regex regex (s:string) =
    let post = post_of_regex regex
    let start = nfa_of_post post
    let result = matching (add_state start []) (List.ofSeq s)
    match List.tryFind (fun a -> a=Match) result with
    | Some _ -> true
    | _ -> false
    
let main (argv:string []) =
    let regex =  argv.[1]
    for i = 2 to (argv.Length - 1) do
        try
            if match_regex regex (argv.[i])
            then printfn "%s" (argv.[i])
        with
            e -> printfn "%A" e

//let argv = System.Environment.GetCommandLineArgs()
//main argv
//main [| ""; "abc(d+)"; "abcdddd" ; "cdef"; "abc" ; "abcd"; |]
