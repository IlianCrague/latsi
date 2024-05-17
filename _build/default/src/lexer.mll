{
open Parser
}

let layout = [ ' ' '\t' ]

rule main = parse
  | layout		{ main lexbuf }
  | '\n' { CR }
  | "IMPRIME"			{ IMPRIME }
  | "SI"			{ SI }
  | "ALORS"    { ALORS }
  | "VAVERS"         { VAVERS }
  | "ENTREE"       { ENTREE }
  | "="     { EQ }
  | "FIN" { FIN }
  | "REM" { REM }
  | "NL" { NL }
  | "+" { PLUS }
  | "-" { MOINS }
  | "*" { MULT }
  | "/" { DIV }
  | "," { COMMA }
  | "<>" { NEQ }
  | "><" { NEQ }
  | "<=" { LTE }
  | "<" { LT }
  | ">" { GT }
  | ">=" { GTE }
  | "(" { PG }
  | ")" { PD }
  | (['A'-'Z'] as x) { VAR(x) }
  |'"' ([^'"']* as s) '"' { STRING s }
  | ['0'-'9']+ as n { INT (int_of_string n) }
  | eof			{ EOF }
  | '\n' eof { EOF }
  | _			{ failwith "unexpected character" }
