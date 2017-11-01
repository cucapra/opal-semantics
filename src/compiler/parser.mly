%{
  open Ast
  open Printf
  open Lexing
%}

%token <string> STR
%token LPAREN RPAREN DOT ASSIGN LBRACE RBRACE SEMICOLON WITH AT DO SKIP HYP
       COMMIT HANDLE MERGE IN IF THEN ELSE TRUE FALSE EQUALS AND OR EOF

%type <Ast.com> com
%type <Ast.sexp> sexp
%type <Ast.bool> bool

%start com

%right SEMICOLON
%right DOT
%right WITH AT HYP ELSE STR IN
%right OR
%right AND

%%

com:  SKIP                               { Skip }
    | LBRACE com RBRACE                  { $2 }
    | com SEMICOLON com                  { Seq ($1, $3) }
    | IF bool THEN com ELSE com          { If ($2, $4, $6) }
    | WITH STR com                       { With ($2, $3) }
    | AT STR com                         { At ($2, $3) }
    | STR ASSIGN HYP com                 { Hyp ($1, $4) }
    | COMMIT STR                         { Commit $2 }
    | HANDLE STR DOT STR ASSIGN STR
             WITH sexp MERGE sexp IN com { Handle ($2, $4, $6, $8, $10, $12) }
    | STR                                { Op $1 }
    | STR DOT STR ASSIGN sexp            { Handle ($1, $3, "__tmp", $5, EmptySet, Op "__tmp" ) }

bool: TRUE               { True }
    | FALSE              { False }
    | sexp EQUALS sexp   { Equals ($1, $3) }
    | sexp IN sexp       { In ($1, $3) }
    | bool AND bool      { And ($1, $3) }
    | bool OR bool       { Or ($1, $3) }
    | LPAREN bool RPAREN { $2 }

sexp: LPAREN RPAREN      { EmptySet }
    | sexp DOT sexp      { Cons ($1, $3) }
    | STR DOT STR        { Var ($1, $3) }
    | LPAREN sexp RPAREN { $2 }
