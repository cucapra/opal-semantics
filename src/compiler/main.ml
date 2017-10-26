open Ast

let parse_com channel =
  let lexbuf = Lexing.from_channel channel in
  (* let _ = Parsing.set_trace true in *)
  try Some (Parser.com Lexer.token lexbuf)
  with Parsing.Parse_error ->
    let pos = lexbuf.Lexing.lex_curr_p in
    let tokstr = Lexing.lexeme lexbuf in
    Format.printf "Syntax error at line %d column %d\n" pos.Lexing.pos_lnum pos.Lexing.pos_cnum;
    Format.printf "Unexpected token \"%s\"\n" tokstr;
    None

let () =
  (* (1) Get file name from command-line arguments. *)
  let _ =
    if Array.length Sys.argv <> 2 then
      (Format.printf "Usage: opal <file>\n";
       exit 0) in

  (* (2) Parse file to an expression. *)
  let file =
    if Array.length Sys.argv = 0 then
      stdin
    else
      open_in (Sys.argv.(1))
  in
  let com =
    match parse_com file with
    | Some com -> com
    | None -> exit 1
  in
  print_endline (output_coq_com com);
  ()
