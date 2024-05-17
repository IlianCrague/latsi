
(* The type of tokens. *)

type token = 
  | VAVERS
  | VAR of (char)
  | STRING of (string)
  | SI
  | REM
  | PLUS
  | PG
  | PD
  | NL
  | NEQ
  | MULT
  | MOINS
  | LTE
  | LT
  | INT of (int)
  | IMPRIME
  | GTE
  | GT
  | FIN
  | EQ
  | EOF
  | ENTREE
  | DIV
  | CR
  | COMMA
  | ALORS

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val input: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.programme)
