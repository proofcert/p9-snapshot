(* Logical constants *)
%token OR
%token NOT
%token FALSE
%token ALL
%token AND
%token IMP
%token IFF
%token EXISTS
(* Tactics *)
%token ASSUMPTION
%token CLAUSIFY
%token RESOLVE
%token FACTOR
%token COPY
%token MERGE
(* Punctuation *)
%token LPAREN
%token RPAREN
%token LBRACK
%token RBRACK
%token COMMA
%token DOT
(* Values *)
%token <string> ID
%token <int> NUM
(* End of input *)
%token EOF

%start <Prover9.step list> proof

%%

(* A proof is a nonempty sequence of clauses.
 *
 * TODO: Assumptions may not be in clausal form; these will have to be treated
 * separately, en passant, and assumed to be clausified. The only exception
 * treated now is the empty clause, false. *)
proof:
  | clauses; EOF { $1 }
  ;

clauses:
  | clause; clauses_opt { $1 :: $2 }
  ;

clauses_opt:
  | clause; clauses_opt { $1 :: $2 }
  |                     { [] }
  ;

(* A clause is a disjunction of literals labeled with a unique numeric
 * identifier and provenance information in the form of a tactic. The empty
 * clause is the logical constant false. *)
clause:
  | NUM; literals_or_false; DOT; LBRACK; tactic; RBRACK; DOT { Prover9.Step($1, $2, $5) }
  ;

literals_or_false:
  | literals { $1 }
  | FALSE    { [] }

literals:
  | literal; literals_opt { $1 :: $2 }
  ;

literals_opt:
  | OR; literal; literals_opt { $2 :: $3 }
  |                           { [] }
  ;

(* A literal is a possibly negated atom, possibly with recursive term arguments
 * and implicit universal quantifiers as uppercase identifiers.
 *
 * TODO: Atoms cannot be uppercase identifiers, but this constraint is not made
 * explicit here.) *)
literal:
  | not_opt; id; arguments_opt { let atom = Prover9.Atom($2, $3) in
                                 if $1 then Prover9.Positive(atom) else Prover9.Negative(atom) }
  ;

not_opt:
  | NOT { false }
  |     { true }
  ;

(* An atom and a term may have a comma-separated list of terms as arguments written
 * inside parentheses. *)
arguments_opt:
  | LPAREN; terms; RPAREN { $2 }
  |                       { [] }
  ;

terms:
  | term; terms_opt { $1 :: $2 }
  ;

terms_opt:
  | COMMA; term; terms_opt { $2 :: $3 }
  |                        { [] }
  ;

(* A term, like an atom, is described as an identifier and optional arguments,
 * themselves terms.
 *
 * TODO: Universally quantified variables are assumed only at the leaves, but
 * not explicitly verified. *)
term:
  | id; arguments_opt { Prover9.Term($1, $2) }
  ;

(* Supported tactics. *)
tactic:
  | ASSUMPTION                                                     { Prover9.Assumption }
  | CLAUSIFY; LPAREN; NUM; RPAREN                                  { Prover9.Clausify($3) }
  | RESOLVE; LPAREN; NUM; COMMA; ID; COMMA; NUM; COMMA; ID; RPAREN { Prover9.Resolve($3, $7) }
  | FACTOR; LPAREN; NUM; COMMA; ID; COMMA; ID; RPAREN              { Prover9.Factor($3) }
  | COPY; LPAREN; NUM; RPAREN; COMMA; MERGE; LPAREN; ID; RPAREN    { Prover9.Merge($3) }
  ;

(* Reserved "namespace" for user declarations, to avoid name clashes. This still
 * does not acount for clashes across examples; all of which share a namespace
 * under this translation. *)
id:
  | ID { $1 ^ "_p9" }
  ;
