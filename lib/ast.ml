exception TypeError of string


type ocaml_type_id =
  | IntTy
  | BoolTy
  | StringTy
  | UnitTy
  | FunTy of ocaml_type_id * ocaml_type_id
  | TupleTy of ocaml_type_id list
  | IdTy of string

type ocaml_unop =
  | NotOp
  | NegateOp

type ocaml_binop =
  | Add
  | Sub
  | Mul
  | Div
  | Modulo
  | Less
  | Equal
  | Concatenate
  | AndOp
  | OrOp


type ocaml_var = (*useful so string literals and variables can be distinguished *)
  | OVar of string

type option_type = (*I know this is just a specific version of option *)
  | Typeyes of ocaml_type_id
  | Typeno

type param_type = (* I realized that type branches and parameter lists were represented exactly the same way, so merged them*)
  | PType of ocaml_var * option_type

type ocaml_binding =
  | OcamlType of ocaml_var * param_type list (*type name * (type name * type contents) *)
  | OcamlLet of bool * ocaml_var * param_type list * option_type * ocaml_expr
and ocaml_expr = (*tried to keep in same order as in grammar *)
  | Letexpr of bool * ocaml_var * param_type list * option_type * ocaml_expr * ocaml_expr (* is_recursive, parameters, type (if there), expr in expr  *)
  | Ifexpr of ocaml_expr * ocaml_expr * ocaml_expr (*If <conditional> then <e1> else <e2 *)
  | Funexpr of param_type list * option_type * ocaml_expr
  | FuncApp of ocaml_expr * ocaml_expr  (* Expr application *)
  | Binopexpr of  ocaml_expr * ocaml_binop * ocaml_expr
  | Unopexpr of ocaml_unop * ocaml_expr
  | Idlit of ocaml_var
  | Intliteral of int
  | Boolliteral of bool
  | Stringliteral of string
  | Tupleliteral of ocaml_expr list
  | EmptyExpr
  | Matchexpr of ocaml_expr * ocaml_match_branch list
and ocaml_match_branch =
  | MBranch of ocaml_var * string list * ocaml_expr
(* frankly, by my conventions, this string list should be an OVar list, but that is considerably harder to parse for little benefit *)




let rec print_ol_prog (ol : ocaml_binding list) : string =
  match ol with
  | hd :: tl -> (print_ol_bind hd) ^ "\n" ^ (print_ol_prog tl)
  | [] -> ""
and print_ol_bind (ol : ocaml_binding) : string =
  match ol with
  | OcamlType (v1, plist) -> "type " ^ print_ol_var v1 ^ " =" ^ String.concat "" (List.map print_ol_type_br plist) ^ ";;"
  | OcamlLet (b1, v1, plist, otype, expr) -> "let " ^ (match b1 with
    | true -> "rec "
    | false -> "") ^ print_ol_var v1 ^ " " ^ String.concat "" (List.map print_let_vars plist) ^ (print_func_ty otype) ^ " = " ^ print_ol_expr expr ^ ";;"
and print_func_ty (ol : option_type) : string =
  match ol with
  | Typeno -> ""
  | Typeyes ty -> " : " ^ print_ol_type ty
and print_ol_var (ol : ocaml_var) : string =
  match ol with
  | OVar str -> str
and print_ol_type_br (ol: param_type) : string =
  match ol with
  | PType (v1, t1) -> "| " ^ print_ol_var v1 ^ (match t1 with
    | Typeno -> ""
    | Typeyes t1 -> " of " ^ print_ol_type t1)
and print_let_vars (ol: param_type) : string =
  match ol with
  | PType (v1, t1) -> "(" ^ print_ol_var v1 ^ (match t1 with
    | Typeno -> ")"
    | Typeyes t1 -> " : " ^ print_ol_type t1 ^ ")")
and print_ol_type (ol : ocaml_type_id) : string =
  match ol with
  | IntTy -> "int"
  | BoolTy -> "bool"
  | StringTy -> "string"
  | UnitTy -> "unit"
  | FunTy (t1, t2) -> print_ol_type t1 ^ "->" ^ print_ol_type t2
  | TupleTy tlist -> String.concat " * " (List.map print_ol_type tlist)
  | IdTy t1 -> t1
and print_ol_expr (ol : ocaml_expr) : string =
  match ol with
  | Letexpr (b1, v1, plist, otype, ex1, ex2)-> "let " ^ (match b1 with
    | true -> "rec "
    | false -> "") ^ print_ol_var v1 ^ " " ^ String.concat "" (List.map print_let_vars plist) ^ print_func_ty otype ^ " = " ^ print_ol_expr ex1 ^ " in " ^ print_ol_expr ex2
  | Ifexpr (ifv, thenv, elsev) -> "If " ^ print_ol_expr ifv ^ " Then " ^ print_ol_expr thenv ^ " Else " ^ print_ol_expr elsev
  | Funexpr (plist, otype, ex1)-> "fun " ^ String.concat "" (List.map print_let_vars plist) ^ print_func_ty otype ^ " -> " ^ print_ol_expr ex1
  | FuncApp (e1, e2) -> "(" ^ print_ol_expr e1 ^ ") (" ^ print_ol_expr e2 ^ ")"
  | Binopexpr (e1, bin, e2) -> "(" ^ print_ol_expr e1 ^ ") " ^ print_binop bin ^ " (" ^ print_ol_expr e2 ^ ")"
  | Unopexpr (uno, e1) -> print_unop uno ^ "(" ^ print_ol_expr e1 ^ ")"
  | Idlit ovar -> print_ol_var ovar
  | Intliteral i -> string_of_int i
  | Boolliteral b -> string_of_bool b
  | Stringliteral s -> "\"" ^ s ^ "\""
  | Tupleliteral t ->  "(" ^ String.concat ", " (List.map print_ol_expr t) ^ ")"
  | EmptyExpr -> "()"
  | Matchexpr (e1, mblist) -> "(match " ^ print_ol_expr e1 ^ " with " ^ String.concat "" (List.map print_match_br mblist) ^ ")"
and print_match_br (ol : ocaml_match_branch) : string =
  match ol with
  | MBranch (ov, varlist, ex) -> "| " ^ print_ol_var ov ^ "(" ^ (String.concat ", " varlist) ^ ") -> " ^ print_ol_expr ex
and print_binop (ol: ocaml_binop) : string =
  match ol with
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Modulo -> "mod"
  | Less -> "<"
  | Equal -> "="
  | Concatenate -> "^"
  | AndOp -> "&&"
  | OrOp -> "||"
and print_unop (ol: ocaml_unop) : string =
  match ol with
  | NotOp -> "not "
  | NegateOp -> "~"
