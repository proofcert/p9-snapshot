type term =
  | Term of string * term list

type atom =
  | Atom of string * term list

type literal =
  | Positive of atom
  | Negative of atom

type clause = literal list

type tactic =
  | Assumption
  | Clausify of int
  | Resolve of int * int
  | Factor of int
  | Merge of int

type step =
  | Step of int * clause * tactic
