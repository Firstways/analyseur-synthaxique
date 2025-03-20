
(* The type of tokens. *)

type token = 
  | VAR of (Syntax.idvar)
  | TRUE
  | TINT
  | THEN
  | TBOOL
  | SEMICOLON
  | RPAR
  | PLUSF
  | PLUS
  | NOT
  | NEQ
  | MULTF
  | MULT
  | MINUSF
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
  | DIVF
  | DIV
  | COMMA
  | COLON

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.programme)
