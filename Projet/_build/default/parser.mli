
(* The type of tokens. *)

type token = 
  | VAR of (Syntax.idvar)
  | TRUE
  | TINT
  | THEN
  | TBOOL
  | SEMICOLON
  | RPAR
  | PLUS
  | NOT
  | NEQ
  | MULT
  | MINUS
  | LPAR
  | LOR
  | LET
  | LESSEQ
  | LESS
  | LAND
  | INT of (int)
  | IN
  | IF
  | GREATEQ
  | GREAT
  | FALSE
  | EQ
  | EOF
  | ELSE
  | DIV
  | COMMA
  | COLON

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.programme)
