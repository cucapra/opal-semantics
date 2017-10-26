{
open Parser
open Printf
exception Eof
exception Err
let incline lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
  lexbuf.Lexing.lex_curr_p <- { pos with
    Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
    Lexing.pos_bol = pos.Lexing.pos_cnum;
  }
}

let id = ['a'-'z' 'A'-'Z' '0'-'9' '_']+
let ws = [' ' '\t']

rule token = parse
| ws       { token lexbuf }
| '\n'     { incline lexbuf; token lexbuf }
| "("      { LPAREN }
| ")"      { RPAREN }
| "."      { DOT }
| ":="     { ASSIGN }
| "{"      { LBRACE }
| "}"      { RBRACE }
| ";"      { SEMICOLON }
| "with"   { WITH }
| "at"     { AT }
| "do"     { DO }
| "skip"   { SKIP }
| "hyp"    { HYP }
| "commit" { COMMIT }
| "handle" { HANDLE }
| "merge"  { MERGE }
| "in"     { IN }
| "if"     { IF }
| "then"   { THEN }
| "else"   { ELSE }
| "true"   { TRUE }
| "false"  { FALSE }
| "="      { EQUALS }
| "&"      { AND }
| "|"      { OR }
| id as v  { STR(v) }
| eof      { EOF }

| _ as c  {
            let pos = lexbuf.Lexing.lex_curr_p in
            printf "Error at line %d column %d\n" pos.Lexing.pos_lnum pos.Lexing.pos_cnum;
            printf "Unrecognized character: [%c]\n" c;
            exit 1
          }
