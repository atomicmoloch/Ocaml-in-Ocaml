open Ast
open Typechecker

exception InterpretError of string

(*I tried to handle the interpreter more like the lambda calculus interpreter
Which reduces each term until it gets an irreducable form
And being careful passing environmental variables instead of using an explicit closure class
Furthermore, limiting *)


type interval =
    | VInt of int
    | VBool of bool
    | VString of string
    | VEmpty
    | VTuple of interval list
    | VTempty of string
    | VFull of string * interval
    | VFun of param_type list * interval
    | VExpr of ocaml_expr (* A currier for expressions - shouldn't be returned except as part of a function *)


let rec print_interval (i : interval) : string =
    match i with
    | VInt i -> string_of_int i
    | VBool b -> string_of_bool b
    | VString s -> s
    | VEmpty -> "()"
    | VTuple ilist -> "(" ^ String.concat ", " (List.map print_interval ilist) ^ ")"
    | VTempty s -> s
    | VFull (s, i1) -> s ^ "(" ^ print_interval i1 ^ ")"
    | VFun (plist, ex1) -> "Fun " ^ String.concat "" (List.map print_let_vars plist) ^ " = " ^ print_interval ex1
    | VExpr ex -> print_ol_expr ex


let rec pairer  (envir : (string * interval) list) (slist : string list) (tlist : interval) : (string * interval) list  =
    match tlist with
    | VTuple tuplist -> (match tuplist with
        | hd :: tl -> (match slist with
            | hds :: tls -> (hds, hd) :: (pairer envir tls (VTuple (tl)))
            | [] ->  raise (InterpretError ("No corresponding value in match branch")))
        | [] -> if (List.length slist = 0) then [] else raise (InterpretError ("No corresponding value in match branch")))
    | _ -> (match slist with
        | hd :: [] -> [(hd, tlist)]
        | _ -> raise (InterpretError ("Mismatch between match pattern and begotten")))

let rec funapp (paramlist : param_type list) (funvar : interval) (valexpr : interval) (funself : (string * interval) list): interval =
    match paramlist with
    | PType (vname, vtype) :: tl -> (match tl with
        | [] -> funapphelper vname valexpr funself funvar
        | _ -> VFun (tl, funapphelper vname valexpr funself funvar)
        )
    | [] -> raise (InterpretError ("Function given extra argument: " ^ print_interval valexpr))
and funapphelper (vname : ocaml_var) (valexpr : interval) (funself : (string * interval) list)  (funvar : interval) : interval =
    match funvar with
    | VExpr ex -> interprex ((print_ol_var vname, valexpr) :: (funself)) ex
    | VFun (plist, ex1) -> VFun (plist, funapphelper vname valexpr funself funvar)
    | VFull (s, i) -> VFull (s, funapphelper vname valexpr funself i)
    | VTuple ilist -> VTuple (List.map (funapphelper vname valexpr funself) ilist)
    | _ -> funvar
and interprex  (envir : (string * interval) list) (ex : ocaml_expr) : interval =
match ex with
  | Letexpr (recbool, ov, plist, otype, ex1, ex2) -> (match plist with
    | [] ->  interprex (((print_ol_var ov), interprex envir ex1) :: envir) ex2
    | _ -> interprex (((print_ol_var ov), VFun (plist, interprex envir ex1)) :: envir) ex2
    )
  | Ifexpr (e1, e2, e3) -> let i1 = interprex envir e1 in (match i1 with
    | VBool b ->  if b then interprex envir e2 else interprex envir e3
    | VExpr ex -> VExpr (Ifexpr (e1, e2, e3))
    | _ -> raise (InterpretError ("Expected bool for if statement, got " ^ print_interval i1)))
  | Funexpr (plist, otype, e1) -> VFun (plist, interprex envir e1)
  | FuncApp (e1, e2) -> let i1 = interprex envir e1 in let i2 = interprex envir e2 in (match i1 with
    | VTempty s -> VFull (s, i2)
    | VFun (plist, oexpr) -> (match e1 with
        | Idlit (OVar fid) -> let funself = [(fid, List.assoc fid envir)] in funapp plist oexpr i2 funself (* Recursive function support *)
        | _ -> funapp plist oexpr i2 []
    )
    | VExpr ex -> (match ex with
        | Idlit ov -> let s = print_ol_var ov in (
        if s = "int_of_string" then (match i2 with
            | VString s -> VInt (int_of_string s)
            | _ -> raise VExpr (FuncApp (e1, e2)) else
        if s = "string_of_int" then (match i2 with
            | VInt s -> VString (string_of_int s)
            | _ -> VExpr (FuncApp (e1, e2)) else
        if s = "print_string" then (match i2 with
            | VString s -> let x = print_string (s ^ "\n") in VEmpty
            | _ -> VExpr (FuncApp (e1, e2)))
        else VExpr (FuncApp (ex, e2)))
        | _ -> VExpr (FuncApp (e1, e2)))
    | _ -> raise (InterpretError ("Function application attempted with non-function variable " ^ print_interval i1)))
  (* Interprex e1 is in case e1 is an idty *)
  | Binopexpr (e1, b1, e2) -> let i1 = interprex envir e1 in let i2 = interprex envir e2 in (match b1 with
    | Add -> (match i1 with
        | VInt n1 -> (match i2 with
            | VInt n2 -> VInt (n1 + n2)
            | _ -> VExpr (ex)
        )
        | _ -> VExpr (ex))
    | Sub -> (match i1 with
        | VInt n1 -> (match i2 with
            | VInt n2 -> VInt (n1 - n2)
            | _ -> VExpr (ex)
        )
        | _ -> VExpr (ex))
    | Mul -> (match i1 with
        | VInt n1 -> (match i2 with
            | VInt n2 -> VInt (n1 * n2)
            | _ -> VExpr (ex)
        )
        | _ -> VExpr (ex))
    | Div -> (match i1 with
        | VInt n1 -> (match i2 with
            | VInt n2 -> VInt (n1 / n2)
            | _ -> VExpr (ex)
        )
        | _ -> VExpr (ex))
    | Modulo -> (match i1 with
        | VInt n1 -> (match i2 with
            | VInt n2 -> VInt (n1 mod n2)
            | _ -> VExpr (ex)
        )
        | _ -> VExpr (ex))
    | Less -> (match i1 with
        | VInt n1 -> (match i2 with
            | VInt n2 -> VBool (n1 < n2)
            | _ -> VExpr (ex)
        )
        | _ -> VExpr (ex))
    | Equal -> (match i1 with
        | VExpr _ -> VExpr (ex)
        | VFun _ -> VExpr (ex)
        | _ -> (match i2 with
            | VExpr _ -> VExpr (ex)
            | VFun _ -> VExpr (ex)
            | _ -> VBool (i1 = i2))
        )
    | Concatenate -> (match i1 with
        | VString s1 -> (match i2 with
            | VString s2 -> VString (s1 ^ s2)
            | _ -> VExpr (ex) )(* tbh this case should never arise, but including nonetheless *)
        | _ -> VExpr (ex) )
    | AndOp -> (match i1 with
        | VBool n1 -> (match i2 with
            | VBool n2 -> VBool (n1 && n2)
            | _ -> VExpr (ex)
        )
        | _ -> VExpr (ex) )
    | OrOp -> (match i1 with
        | VBool n1 -> (match i2 with
            | VBool n2 -> VBool (n1 || n2)
            | _ -> VExpr (ex)
        )
        | _ -> VExpr (ex) )
    )
  | Unopexpr (u1, e1) -> let i1 = interprex envir e1 in (match u1 with
    | NotOp -> (match i1 with
        | VBool b1 -> VBool (not b1)
        | _ -> VExpr (ex))
    | NegateOp -> (match i1 with
        | VInt n1 -> VInt (-n1)
        | _ -> VExpr (ex))
        )
  | Idlit ov -> (match ov with
    | OVar s -> (match List.assoc_opt s envir with
        | Some e1 -> e1
        | None -> VExpr (Idlit (OVar s)))) (*todo: figure out what to do here *)
  | Intliteral i -> VInt i
  | Boolliteral b -> VBool b
  | Stringliteral s -> VString s
  | Tupleliteral tlist -> VTuple (List.map (interprex envir) tlist)
  | EmptyExpr -> VEmpty
  | Matchexpr (e1, mblist) -> let i1 = interprex envir e1 in (match i1 with
    | VFull (s, inv) -> vollmap envir s inv mblist
    | VTempty s -> vemptymap envir s mblist
    | _ -> (match i1 with
        | VExpr _ -> VExpr ex
        | _ -> raise (InterpretError ("Invalid input to match branch: " ^ print_interval i1))
    )
  )
and vemptymap (envir : (string * interval) list) (s : string) (mblist : ocaml_match_branch list) : interval =
    match mblist with
    | hd :: tl -> (match hd with
        | MBranch (ov, slist, oex) -> if (s = print_ol_var ov) || (print_ol_var ov = "_") then interprex envir oex else vemptymap envir s tl)
    | [] -> raise (InterpretError ("Value " ^ s ^ " absent in match branch"))
and vollmap (envir : (string * interval) list) (s : string) (ilist : interval) (mblist : ocaml_match_branch list) : interval =
    match mblist with
    | hd :: tl -> (match hd with
        | MBranch (ov, slist, oex) -> if (s = print_ol_var ov) || (print_ol_var ov = "_") then interprex (pairer envir slist ilist @ envir) oex else vollmap envir s ilist tl)
    | [] -> raise (InterpretError ("Value " ^ s ^ " absent in match branch"))



let param_to_interval p =
    match p with
    | PType (ov, tyo) -> (print_ol_var ov, VTempty (print_ol_var ov))

let interbind (envir : (string * interval) list) (ex : ocaml_binding) : (interval list) * ((string * interval) list) =
    match ex with
    | OcamlType (ovar, plist) -> ([], List.map (param_to_interval) plist)
    | OcamlLet (rbool, ov, plist, otype, e1) -> (match plist with
        | [] -> let i1 = interprex envir e1 in ([i1], [(print_ol_var ov, i1)])
        | _ -> let i1 = VFun (plist, (interprex envir e1)) in ([i1], [(print_ol_var ov, i1)]))


let rec interprog (envir : (string * interval) list)  (prog : ocaml_binding list) : interval list =
    match prog with
    | hd :: tl -> let (i1, en1) = interbind envir hd in i1 @ (interprog (en1 @ envir) tl)
    | [] -> []

let interpret (prog : ocaml_binding list) : interval list =
    interprog [] prog

let interp_and_print (prog : ocaml_binding list) =
    print_string ("\n" ^ (String.concat "\n" (List.map print_interval (interpret (prog)))) ^ "\n")
