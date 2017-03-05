{
  open Lexing
  open Parser

  exception SyntaxError of string
}

(* In identifiers, we group together bound variables, by convention and
 * implicitly uppercase, and constructors. *)
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*

(* Clause identifiers are strictly positive, and the minus sign is reserved for
 * negation. *)
let num = ['1'-'9'] ['0'-'9']*

(* While we expect a clause to be self-contained in its own line, it is simpler
 * to exploit the grammar and group all whitespace together. *)
let white = [' ' '\t' '\r' '\n']+

rule read = parse
  (* Whitespace *)
  | white        { read lexbuf }
  (* Logical constants *)
  | '|'          { OR }
  | '-'          { NOT }
  | "$F"         { FALSE }
  | "all"        { ALL }
  | '&'          { AND }
  | "->"         { IMP }
  | "<->"        { IFF }
  | "exists"     { EXISTS }
  (* Tactics *)
  | "assumption" { ASSUMPTION }
  | "clausify"   { CLAUSIFY }
  | "resolve"    { RESOLVE }
  | "factor"     { FACTOR }
  | "copy"       { COPY }
  | "merge"      { MERGE }
  (* Punctuation *)
  | '('          { LPAREN }
  | ')'          { RPAREN }
  | '['          { LBRACK }
  | ']'          { RBRACK }
  | ','          { COMMA }
  | '.'          { DOT }
  (* Values *)
  | id as str    { ID (str) }
  | num as str   { NUM (int_of_string str) }
  (* End of input *)
  | eof          { EOF }
  (* Errors *)
  | _ as char    { raise (SyntaxError (String.make 1 char)) }
