open OUnit2
open Ocaml_lite.Lexer
open Ocaml_lite.Ast
open Ocaml_lite.Parser
open Ocaml_lite.Typechecker
open Ocaml_lite.Interpreter


(* let parse_tests = "test suite for parser" >::: [
    "let" >::
    (fun _ -> assert_equal ~printer:print_oc_expr
        (Oprogram ([OcamlLet (false, Ovar ("test"), [Param ("t1", Typeyes (BoolTy)], Typeyes(BoolTy), Boolliteral (true)])
        (parse "let test (t1 : bool) : bool = true;;"));
    "type" >::
    (fun _ -> assert_equal ~printer:print_oc_expr
        (Oprogram ([OcamlType ("int list", [OTypeBr (Ovar ("Nil"), Typeno), OTypeBr (Ovar ("Cons"), Typeyes (TupleTy (IntTy, IdTy ("int_list"))))])])
        (parse "type int_list =
        | Nil
        | Cons of int * int_list ;;"));
    "match" >::
    (fun _ -> assert_equal ~printer:print_oc_expr
        (Oprogram ([OcamlLet (false, Ovar ("test"), [Param ("m", Typeyes (IdTy ("character")))], Typeyes(BoolTy), Matchexpr (Ovar ("Equal"), [], Boolliteral (true), Mexpr_expr (Ovar ("Colon"), [], Boolliteral (false), Mexpr_base)))])
        (parse "let matchtest (m : character) : bool = match m with
        | Equal -> true
        | Colon -> false"));
  ]*)
  (*Parse tests to add:
  Binary op tests (let test (t1 : int) (t2 : int) : int = t1 * t2;;)
  Unary op tests (let test (t1 : bool) : bool = not t1;;)
  Match with variables (let test (t1 : typ) : int = match t1 with | thing a, b -> a * b;;)
  Match with no branches (should fail) (let test (t1 : typ) : int = match t1 with;;)
  Let inside of let (let test (t1 : int) : int = let t2 = 5 in t1 * t2)
*)

(*
Typecheck tests to add:
let test (t1 : bool) : bool = true;;
let test (t1 : int) (t2 : int) : int = t1 * t2;;
(should fail) let test (t1 : typ) : int = match t1 with | thing1 -> 4 | thing2 -> true;;
(should fail) let test (t1 : int) (t2 : int) : int = t1 == t2;;
(should fail) let test (t1 : int) (t2 : bool) : int = t1 * t2;;
let test (t1 : int) : bool = let t1 = true in t1;;
(should fail) let test (t1 : int) : int = let t1 = true in t1;;
*)

(*
Interpreter tests
let test (t1 : bool) : bool = true;;
let test (t1 : int) (t2 : int) : int = t1 * t2;;
let test (t1 : int) : bool = let t1 = true in t1;;
type typ: | thing of int * int;; let test (t1 : typ) : int = match t1 with | thing a, b -> a * b;;
let test (t1 : int) : int = let t2 = 5 in t1 * t2
Cumalative interpreter test: put in the entire Ocaml-lite example code from the 10/23 in-class notes;;
*)

(*assert_equal (parse "type a = | b;;") [OcamlType (OVar "a", [PType (OVar "b", Typeno)])]*)

let test_string (s : string) =
  print_string ("\n" ^ (print_ol_prog (parse s)) ^ "\n")

let tc_string (s : string) =
  print_string ("\n" ^ (String.concat "\n" (List.map print_tc (typecheck_prog (parse s)))) ^ "\n")

let test_interpret (s : string) =
  print_string ("\n" ^ (String.concat "\n" (List.map print_interval (interpret (parse s)))) ^ "\n")

let behemoth = "

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
"

let basic_type_test _ =
  test_string "type a = | b;;"

let basic_let_test _ =
  test_string "let a = () ;;"

let factorial _ =
  test_string "let rec fact n = if n = 0 || n = 1 then 1 else (fact (n - 1)) + (fact (n - 2)) ;;"

let let_lessthan _ =
  test_string "let a = b < c ;;"

let arith_test _ =
  test_string "let a = b * c + c * a;;"

let complex_arith _ =
  test_string "let a = b * c + d mod e / ~f - g ;;"

let the_behemoth _ =
  test_string behemoth

let letinletin_parse _ =
  test_string "let f = let x = 1 in x;;"

let funtest_parse _ =
  test_string "let f = fun x => 3;;"



let basic_let_tc _ =
  tc_string "let a x y = x * y ;;"

let basic_fun_tc _ =
  tc_string "let f = fun x => 3;;"

let basic_match_tc _ =
  tc_string "let f b = match b with | True => False | False => True;;"

let basic_match_tc_typed _ =
  tc_string "let f (b : bool) = match b with | True => false | False => true;;"

let basic_letin_tc _ =
  tc_string "let f = let x = 1 in x;;"

let match_letin_tc _ =
  tc_string "let f n = let y = thing in match y with | z => 3 | x => 4;;"

let custom_type_simple_tc _ =
  tc_string "type x = | y;; let b z = y;;"

let simple_interpret _ =
  test_interpret "let x = 5 * 5;;"

let function_interaction _ =
  test_interpret "let dub x = 2 * x;;  let y = dub 2;;"

let custom_type_match _ =
  test_interpret "type a = | thing;; let a = let b = thing in match b with | thing => 2;;"

let recursive_interpret _ =
  test_interpret "let fact n = if 1 = n then 1 else n * (fact (n - 1));; let x = fact 3;;"

let interpret_file _ =
  test_interpret "
  let add x y = x + y;;
let absolute_value x = if x < 0 then ~ x else x;;

type day =
 | Monday
 | Tuesday
 | Wednesday
 | Thursday
 | Friday
 | Saturday
 | Sunday;;

let weekday (w : day) : bool =
    match w with
    | Saturday => false
    | Sunday => false
    | _ => true;;

type int_option =
 | Hasint of int
 | Noint;;

let default (i : int) (o : int_option) : int =
    match o with
    | Hasint vl => vl
    | Noint => i;;

let test_day = weekday Monday;;

let test_weekend = weekday Saturday;;

let test_default = default 1 (Hasint 2);;

let test_default_2 = default 1 (Noint);;
"

let test_behemoth _ =
  test_interpret behemoth

let tests = "test suite for ocaml_lite" >::: [
     (* Lexer.lex_tests;
    parse_tests *)
    (*"basic type" >:: basic_type_test;
    "basic let" >:: basic_let_test;
    "factorial" >:: factorial;
    "let lessthan" >:: let_lessthan;
    "arith" >:: arith_test;
    "complex arith" >:: complex_arith;
    "behemoth" >:: the_behemoth;
    "let in test" >:: letinletin_parse;
    "fun test" >:: funtest_parse; *)

   (* (* typecheck tests *)
    "basic let" >:: basic_let_tc;
     "basic fun" >:: basic_fun_tc;
     "b match" >:: basic_match_tc;
     "b match typed" >:: basic_match_tc_typed;
     "letin type" >:: basic_letin_tc;
     "match letin" >:: match_letin_tc;
     "custom type simple" >:: custom_type_simple_tc; *)

     (* Interpret tests *)
    "simple interpret" >:: simple_interpret;
    "fun interaction" >:: function_interaction;
    "custom type match" >:: custom_type_match;
       "Recursive simple" >:: recursive_interpret;
       "interpret file" >:: interpret_file;
       "behemoth" >:: test_behemoth;


  ]

let _ = run_test_tt_main tests
