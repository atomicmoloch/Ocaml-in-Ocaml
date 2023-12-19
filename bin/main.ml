let parse = fun _ -> Ocaml_lite.Lexer.parse
let typecheck = fun _ -> Ocaml_lite.Typechecker.typecheck_prog
let interpret = fun _-> Ocaml_lite.Interpreter.interp_and_print

let () =
  if Array.length Sys.argv <> 2
  then failwith "Expected exactly one command line argument"
  else
    let ch = In_channel.open_text Sys.argv.(1) in
    let text = In_channel.input_all ch in
    let () = In_channel.close ch in
    let ast = parse text in
    interpret ast
