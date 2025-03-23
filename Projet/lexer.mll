(* Belouin Eliot & Boyenval Louis-Marie 684i *)

{
  open Lexing
  open Parser

  exception SyntaxError of string

  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
      lexbuf.lex_curr_p <-
        { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }
}

let space = [' ' '\t' '\n' '\r']
let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']
let ident = ['a'-'z'] (alpha | '_' | '\'' | digit)*
let integer = digit+

rule token = parse
  | '\n'  { newline lexbuf; token lexbuf }
  | space  { token lexbuf }
  | "(*"  { comment 0 lexbuf }

  | '=' { EQ }

  | '+'  { PLUS }
  | '-'  { MINUS }
  | '*'  { MULT }
  | '/'  { DIV }

  | "+."  { PLUSF }
  | "-."  { MINUSF }
  | "*."  { MULTF }
  | "/."  { DIVF }

  | "true" { TRUE }
  | "false" { FALSE }
  | "&&" { LAND }
  | "||" { LOR }
  | "not" { NOT }
  | ">" { GREAT }
  | ">=" { GREATEQ }
  | "<" { LESS }
  | "<=" { LESSEQ }
  | "<>" { NEQ }
  | "!=" { NEQ }

  | "let"  { LET }
  | "in"  { IN }


  | "if" { IF }
  | "then" { THEN }
  | "else" { ELSE }


  | "int" { TINT }
  | "bool" { TBOOL }
  | "float" { TFLOAT }
  | "unit" { TUNIT }
  | "print_int" { PRINT_INT }


  | '('  { LPAR }
  | ')'  { RPAR }
  | ','  { COMMA }
  | ':'  { COLON }
  | ';' {SEMICOLON}
  
  | eof  { EOF }


  | integer as n  { INT (int_of_string n) }
  | integer '.' integer? as f  { FLOAT (float_of_string f) }
  | ident as id  { VAR id }

  | _  { raise Error }

and comment depth = parse
  | '\n'  { newline lexbuf; comment depth lexbuf }
  | "(*"  { comment (depth + 1) lexbuf }
  | "*)"
    {
      match depth with
      | 0 -> token lexbuf
      | _ -> comment (depth - 1) lexbuf
    }
  | eof     { raise Error }
  | _       { comment depth lexbuf }
