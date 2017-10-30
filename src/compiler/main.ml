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

let assert_idempotent com =
  let out_str = output_opal_com com in
  let (tmp_file_name, tmp_file_out) = Filename.open_temp_file "opal" "idempotence" in
  output_string tmp_file_out out_str;
  close_out tmp_file_out;
  match parse_com (open_in tmp_file_name) with
  | Some reparsed ->
     let reout_str = output_opal_com reparsed in
     if out_str <> reout_str then (
       print_endline "Input:\n";
       print_endline out_str;
       print_endline "\n";
       print_endline "did not match output:\n";
       print_endline reout_str;
       exit 1
     ) else
       ()
  | None ->
     print_endline "Could not reparse:\n";
     print_endline out_str;
     exit 1

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
  assert_idempotent com;
  print_endline (output_coq_com com);
  ()
