
(* The type of tokens. *)

type token = 
  | VAR of (Syntax.idvar)
  | TUNIT
  | TRUE
  | TINT
  | THEN
  | TFLOAT
  | TBOOL
  | SEMICOLON
  | RPAR
  | PRINT_INT
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
  | FLOAT of (float)
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
