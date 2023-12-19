open Ast

exception TypeError of string

let split l =
  (List.map (fun (a, _) -> a) l,
   List.map (fun (_, b) -> b) l)
let split_s l =
  ((fun (a, _) -> a) l,
   (fun (_, b) -> b) l)

let next_var = ref 0

let fresh_var (_ : unit) : string =
  let () = next_var := !next_var + 1 in
  "x$" ^ string_of_int !next_var

type tc_type =
| Mono of ocaml_type_id
| Poly of (string list) * ocaml_type_id

let tc_to_oc (ty : tc_type) : ocaml_type_id =
    match ty with
    | Mono ty -> ty

let print_tc (tc: tc_type) : string =
    match tc with
    | Mono ty -> print_ol_type ty

type cstraint =
| CEq of tc_type * ocaml_type_id
| TEq of tc_type * tc_type
| Exists of string
| TType of string * (ocaml_type_id) (* Represents match branches and user defined types*)


let rec tc_expr (e: ocaml_expr) : (cstraint list * tc_type) =
match e with
| Letexpr (rval, ov, pl, ty, ex1, ex2) -> if
(List.length pl) = 0 then let (cf, tf) = tc_expr ex1 in
let (ce, te) = tc_expr ex2 in
((TEq (Mono(IdTy (print_ol_var ov)), tf)) :: (cf @ ce), te)
else let (cf, tf) = (tc_namedfun ov pl ty ex1) in
let (ce, te) = tc_expr ex2 in ((TEq (Mono(IdTy (print_ol_var ov)), tf)) :: (cf @ ce), te)
| Funexpr (p, o, e) -> tc_fun p o e
| Intliteral _ -> ([], Mono (IntTy))
| Boolliteral _ -> ([], Mono (BoolTy))
| Stringliteral _ -> ([], Mono (StringTy))
| EmptyExpr -> ([], Mono (UnitTy))
| Idlit (OVar id) -> ([Exists (id)], Mono (IdTy (id)))
| Tupleliteral elist -> let (c1, e1) = split (List.map tc_expr elist) in (List.concat c1, Mono(TupleTy (List.map tc_to_oc e1)))
| Ifexpr (b1, e1, e2) ->
let (ce1, te1) = tc_expr e1 in
let (ce2, te2) = tc_expr e2 in
let (cb1, tb1) = tc_expr b1 in
let estraits = List.concat [ce1; ce2; cb1] in
let fvar = Mono (IdTy (fresh_var ())) in ((CEq (tb1, BoolTy)) :: TEq (te1, fvar) :: TEq (te2, fvar) :: estraits, fvar)
| Binopexpr (e1, b, e2) ->
( let (ce1, te1) = tc_expr e1 in
let (ce2, te2) = tc_expr e2 in
let estraits = List.concat [ce1; ce2] in
match b with
    | Less -> (CEq (te1, IntTy) :: CEq (te2, IntTy) :: estraits, Mono (BoolTy))
    | Equal -> (TEq (te1, te2) :: estraits, Mono (BoolTy))
    | AndOp -> (CEq (te1, BoolTy) :: CEq (te2, BoolTy) :: estraits, Mono (BoolTy))
    | OrOp -> (CEq (te1, BoolTy) :: CEq (te2, BoolTy) :: estraits, Mono (BoolTy))
    | Concatenate -> (CEq (te1, StringTy) :: CEq (te2, StringTy) :: estraits, Mono (StringTy))
    | _ -> (CEq (te1, IntTy) :: CEq (te2, IntTy) :: estraits, Mono (IntTy))
    )
| Matchexpr (ex, blist) ->
let branch_ty = Mono (IdTy (fresh_var())) in
(List.concat (List.map (match_constraints branch_ty) blist), branch_ty)
| FuncApp (e1, e2) ->
let fv = fresh_var () in
let (ce1, te1) = tc_expr e1 in
let (ce2, te2) = tc_expr e2 in
(TEq (Mono (FunTy (tc_to_oc te2, IdTy fv)), te1) :: (ce1 @ ce2), Mono (IdTy fv))
and tc_binding (e : ocaml_binding) : (cstraint list * tc_type) =
    match e with
    | OcamlType (vname, plist) -> (List.concat (List.map (param_to_TType (Mono (IdTy (print_ol_var vname)))) plist), Mono (IdTy (print_ol_var vname)))
    | OcamlLet (rval, ov, pl, ty, ex1) -> if (List.length pl) = 0
    then let (cf, tf) = tc_expr ex1 in  ((TEq (Mono(IdTy (print_ol_var ov)), tf) :: cf), tf)
    else (tc_namedfun ov pl ty ex1)
and param_to_TType (tt : tc_type) (o : param_type) : cstraint list =
    match o with
    | PType (vr, otype) -> (match otype with
        | Typeno -> [CEq (tt, IdTy (print_ol_var vr)); TType (print_ol_var vr, TupleTy [])] (* Represents user types without variable with an empty tupletype - not ideal, but I got myself into a bind*)
        | Typeyes t -> [CEq (tt, IdTy (print_ol_var vr)); TType (print_ol_var vr, t)])
and match_constraints (branch_ty : tc_type) (blist : ocaml_match_branch) : cstraint list =
    match blist with
    | MBranch (v, slist, oexpr) -> let (co, tco) = tc_expr (oexpr) in
    (TEq (branch_ty, tco)) :: (TType (print_ol_var v, (TupleTy (List.map (fun x -> IdTy (x)) slist)))) :: co
and tc_param (p: param_type list) : (cstraint list * tc_type) =
match p with
| (PType (v, op)) :: [] -> (match op with
    | Typeno -> ([], Mono (IdTy (print_ol_var v)))
    | Typeyes t -> ([CEq (Mono (IdTy (print_ol_var v)), t)], Mono (IdTy (print_ol_var v)))
)
| (PType (OVar v, op)) :: tail -> ( let (ctail, ttail) = tc_param tail in match op with
    | Typeno -> (ctail, Mono (FunTy ((IdTy v), tc_to_oc ttail)))
    | Typeyes t -> (ctail @ [CEq ((Mono (IdTy v)), t)],  Mono (FunTy ((IdTy v), tc_to_oc ttail)))
)
(* let decs with no arguments shouldn't be processed as functions *)
and tc_fun (p : param_type list) (o : option_type) (e : ocaml_expr) : (cstraint list * tc_type) =
    let (pcon, pty) = tc_param p in let (econ, ety) = tc_expr e in
    match ety with
    | Mono ty -> (match o with
        | Typeno -> (pcon @ econ, Mono (FunTy (tc_to_oc (pty), ty)))
        | Typeyes ty2 -> ((CEq (ety, ty2)) :: (pcon @ econ), Mono (FunTy (tc_to_oc (pty), ty)))
        (* might need to redo *)
    )
and tc_namedfun (ov : ocaml_var) (p : param_type list) (o : option_type) (e : ocaml_expr) : (cstraint list * tc_type) =
match ov with
| OVar a -> let (con, ty) = tc_fun p o e in ((TEq (Mono(IdTy (a)), ty)) :: con, ty)



let rec get_replacements (cs : cstraint) : (ocaml_type_id * ocaml_type_id) list =
match cs with
| CEq (tct, oct) -> (match tct with
    | Mono (tt) -> if (tt = oct) then [] else (match oct with
        | IdTy id -> (match tt with
            | IdTy id2 -> [(IdTy id, IdTy id2)]
            | _ -> get_replacements (CEq (Mono(oct), tt))) (* If CEq becomes constructed backwards from replacements, this code catches it *)
        | _ -> (
    match tt with
        | IdTy id -> [(IdTy id, oct)]
        | FunTy (tt1, tt2) -> (match oct with
            | FunTy (ot1, ot2) -> (get_replacements (CEq (Mono(tt1), ot1))) @ (get_replacements (CEq (Mono(tt2), ot2)))
            | _ -> raise (TypeError (print_ol_type tt ^ " not equals " ^ print_ol_type oct)))
        | TupleTy tlist -> (match oct with
            | TupleTy olist -> List.concat (List.map tuplehelper(List.combine tlist olist))
            | _ -> raise (TypeError (print_ol_type tt ^ " not equals " ^ print_ol_type oct)))
        | _ -> raise (TypeError (print_ol_type tt ^ " not equals " ^ print_ol_type oct)))))
| TEq (tct1, tct2) -> (match tct2 with
    | Mono m -> get_replacements (CEq (tct1, m))) (*placeholder*)
| Exists _ -> [] (* exist constraints handled in type_replace_cs *)
| TType (tct, tlist) -> [(IdTy tct, tlist)] (* Problem here: to fix - figure out a way to distinguish between custom types in match branches and custom types that are being returned in variables - since the first needs their tuples to be equivocated with the custom type underlying type, and the other cannot be*)
and tuplehelper (t : (ocaml_type_id * ocaml_type_id)) : (ocaml_type_id * ocaml_type_id) list =
    let (tl, ol) = split_s t in get_replacements (CEq ((Mono (tl)), ol))


let rec type_replace (rlist : (ocaml_type_id * ocaml_type_id)) (ex : tc_type) : tc_type =
    let (replacee, replacer) = split_s rlist in
    match ex with
    | Mono ty -> if ty = replacee then Mono(replacer) else
        (match ty with
        | FunTy (t1, t2) -> Mono(FunTy (tc_to_oc (type_replace rlist (Mono (t1))), tc_to_oc (type_replace rlist (Mono(t2)))))
        | TupleTy tlst -> Mono(TupleTy (List.map tc_to_oc (List.map (type_replace rlist) (List.map (fun t -> Mono(t)) tlst)))) (* I'm aware this is horrid, but the Mono class is too deeply used to be easily deleted, no matter how unnecessary it is *)
        | _ -> ex

        )

let type_replace_cs (ex : cstraint) (rlist : (ocaml_type_id * ocaml_type_id)) : cstraint list =
(* Returns cstraint list to facilitate exists constraints*)
    let (replacee, replacer) = split_s rlist in
    match ex with
    | CEq (t1, o1) -> [CEq ((type_replace (replacee, replacer) t1 ), o1)]
    | TEq (t1, t2) -> [TEq ((type_replace (replacee, replacer) t1), (type_replace (replacee, replacer) t2))]
    | TType (tn, tlist) -> (match replacee with
        | IdTy t -> if tn = t then [CEq (Mono (tlist), replacer)] else [ex]
        | _ -> [ex])
    | Exists s -> (match replacee with
        | IdTy v -> if v = s then [] else [ex])


let type_replace_cs_helper (rlist : (ocaml_type_id * ocaml_type_id) list ) (ex : cstraint) : cstraint list = (* Curries for type_replace_cs *)
    List.concat (List.map (type_replace_cs ex) rlist)

(* to make sure there are no contradictory replacements *)
let rec consist_checker (ls : (ocaml_type_id * ocaml_type_id) list) : cstraint list=
    match ls with
    | hd :: tl -> let (i, v) = split_s hd in (match (List.assoc_opt i tl) with
        | None -> consist_checker tl
        | Some v2 -> (CEq (Mono(v), v2)) :: (consist_checker tl)
        )
    | [] -> []

let rec get_replacements_helper (cl : cstraint list) : (ocaml_type_id * ocaml_type_id) list=
    match cl with
    | hd :: tl -> let (el) = get_replacements hd in el @ get_replacements_helper(List.concat (List.map (type_replace_cs_helper el) tl))
    | [] -> []

let rec replacements_consistency (cl : cstraint list) : (ocaml_type_id * ocaml_type_id) list=
    let rlist = get_replacements_helper cl in
    let cons = consist_checker rlist in
    rlist

let rec type_replacement_currier (rlst : (ocaml_type_id * ocaml_type_id) list) (tlst : tc_type list) : tc_type list =
    match rlst with
    | hd :: tl -> type_replacement_currier tl (List.map (type_replace hd) tlst)
    | [] -> tlst

let typecheck_prog (ol : ocaml_binding list) : tc_type list =
    let (clstlst, blst) = List.split (List.map tc_binding ol) in
    let clst = List.concat clstlst in
    type_replacement_currier (replacements_consistency clst) blst

