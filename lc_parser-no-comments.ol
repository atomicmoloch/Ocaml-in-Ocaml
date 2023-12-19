
type token =
  | Id of string
  | Lambda
  | Dot
  | LParen
  | RParen ;;  (* Note that we need ;; to separate declarations *)

type tok_list =
  | Nil
  | Cons of token * tok_list ;;

type expr =
  | Var of string
  | Abs of string * expr
  | App of expr * expr
  | Error ;;

let rec expr_to_string (ex : expr) : string = match ex with
  | Var id => \"Var \" ^ id
  | Abs (x, f) => \"Abs (\" ^ x ^ \", \" ^ expr_to_string f ^ \")\"
  | App (e1, e2) => \"App (\" ^ expr_to_string e1 ^ \", \" ^ expr_to_string e2 ^ \")\"
  | Error => \"Error\" ;;


type pair =
  | Pair of expr * tok_list ;;

let rec has_error (ex : expr) : bool = match ex with
  | Var id => false
  | Abs (x, f) => has_error f
  | App (e1, e2) => has_error e1 || has_error e2
  | Error => true ;;


type parse_mode =
  | Expr
  | Aexpr
  | Item ;;

let rec parse_help (mode : parse_mode) (src : tok_list) : pair =

  let expr (src : tok_list) : pair = match src with
    | Nil => parse_help Aexpr src
    | Cons (hd, tl) => (match hd with
      | Id id => parse_help Aexpr src
      | Dot => parse_help Aexpr src
      | LParen => parse_help Aexpr src
      | RParen => parse_help Aexpr src
      | Lambda => (match tl with
        | Nil => parse_help Aexpr src
        | Cons (hd2, tl2) => (match hd2 with
          | Lambda => parse_help Aexpr src
          | Dot => parse_help Aexpr src
          | LParen => parse_help Aexpr src
          | RParen => parse_help Aexpr src
          | Id id => (match tl2 with
            | Nil => parse_help Aexpr src
            | Cons (hd3, tl3) => (match hd3 with
              | Id id => parse_help Aexpr src
              | Lambda => parse_help Aexpr src
              | LParen => parse_help Aexpr src
              | RParen => parse_help Aexpr src
              | Dot => (match parse_help Expr tl3 with
                | Pair (ex, rest) => Pair (Abs (id, ex), rest))))))) in

  let aexpr (src : tok_list) : pair =
    let rec helper ex src = match src with
      | Nil => Pair (ex, src)
      | Cons (hd, tl) => (match hd with
        | Id id => (match parse_help Item src with
          | Pair (i, r) => helper (App (ex, i)) r)
        | Lambda => Pair (ex, src)
        | Dot => Pair (ex, src)
        | LParen => (match parse_help Item src with
          | Pair (i, r) => helper (App (ex, i)) r)
        | RParen => Pair (ex, src)) in
    match parse_help Item src with
    | Pair (e1, r) => helper e1 r in

  let item (src : tok_list) : pair = match src with
    | Nil => Pair (Error, Nil)
    | Cons (hd, tl) => (match hd with
      | Id id => Pair (Var id, tl)
      | Lambda => Pair (Error, Nil)
      | Dot => Pair (Error, Nil)
      | LParen => (match parse_help Expr tl with
        | Pair (e, r2) => (match r2 with
          | Nil => Pair (Error, Nil)
          | Cons (hd2, rest) => (match hd2 with
            | Id id => Pair (Error, Nil)
            | Lambda => Pair (Error, Nil)
            | Dot => Pair (Error, Nil)
            | LParen => Pair (Error, Nil)
            | RParen => Pair (e, rest))))
      | RParen => Pair (Error, Nil)) in

  match mode with
  | Expr => expr src
  | Aexpr => aexpr src
  | Item => item src ;;

let parse_expr (src : tok_list) : expr =
  match parse_help Expr src with
  | Pair (ex, rest) => (match rest with
    | Nil => if has_error ex then Error else ex
    | Cons (hd, tl) => Error) ;;

let source : tok_list =
  Cons (LParen, Cons (Lambda, Cons (Id \"x\", Cons (Dot, Cons (Id \"x\",
  Cons (RParen, Cons (Id \"y\", Nil))))))) ;;

let ast : expr = parse_expr source ;;
let print : unit = print_string (expr_to_string ast) ;;
