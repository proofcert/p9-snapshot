open Prover9
(* NOTE: open Printf *)

(* Generate AST from proof script. *)
let parse lexbuf =
  try
    Parser.proof Lexer.read lexbuf
  with
  | Lexer.SyntaxError str -> Printf.eprintf "Syntax error: %s\n%!" str ; exit 1
  | Parser.Error          -> Printf.eprintf "Parser error\n%!"         ; exit 1

(* Remove assumptions that have been clausified, and are therefore not in normal
 * form, as requisite for the FPC definition. If there are no guarantees that
 * applying clausify on an assumption, N, will generate as many clausify(N)
 * steps as there are clauses resulting from normalizing that assumption,
 * possibly because they are not used in the derivation, we will be certifying a
 * slightly different, more general property.
 *
 * Alternatives involve restricting input to normal form, over which we have no
 * control, or verifying and, if necessary, completing the computation of the
 * normal forms, but these fall outside the scope of this transformation. *)
let clean steps =
  let is_clausified (Step(source, _, tactic)) =
    (* A step N has been clausified if it is an assumption and there are any
     * steps resulting from the clausify tactic on N. *)
    let derived_clause (Step(_, _, tactic)) =
      tactic = Clausify(source)
    in
    tactic = Assumption && List.exists derived_clause steps
  in
  (* Remove steps that have been clausified. *)
  List.filter (fun step -> not (is_clausified step)) steps

(* There are no guarantees that assumptions and clausifications, that is to say
 * the sources of input clauses to the resolution proof, will appear in order.
 * However, such a separation is required by the various resolution certificates
 * in varying degrees. Steps are filtered in two lists of initial and derived
 * steps, respecting otherwise the given order. *)
let reorder steps =
  let is_initial (Step(_, _, tactic)) = match tactic with
    | Assumption | Clausify(_) -> true
    | _ -> false
  in
  List.partition is_initial steps

(* Helper to determine if a term represents a variable. Assumed to be
 * first-order, in which case arguments are ignored (there should be none).
 *
 * NOTE: This is used to simplify treatment where the function is used. If
 * proof scripts are not trusted, enforce these restrictions here, as well. *)
let is_var (Term(name, _)) =
  let c = String.get name 0 in
  'A' <= c && c <= 'Z'

(* Find universally quantified variables in a clause, as uppercase identifiers.
 * All are assumed to be in leaf position, without arguments, and of type i.
 *
 * NOTE: To an extent, this traversal mimics the original pass of the parser. An
 * alternative would include this eigenvariable information in the AST, although
 * it is redundant and strictly derived from it. *)
let clause_eigenvars clause =
  (* Use a hash table as set, here shared by the various traversal functions. *)
  let set = Hashtbl.create 10 in
  let add str = if not (Hashtbl.mem set str) then Hashtbl.add set str () in
  (* Recursive traversal of AST nodes down to term leaves. *)
  let rec term_eigenvars (Term(name, args) as term) =
    if is_var term then add name else List.iter term_eigenvars args
  in
  let atom_eigenvars (Atom(_, args)) =
    List.iter term_eigenvars args
  in
  let literal_eigenvars = function
    | Positive(atom) | Negative(atom) -> atom_eigenvars atom
  in
  List.iter literal_eigenvars clause ;
  (* Return an ordered list from the hash. *)
  [] |>
  Hashtbl.fold (fun v _ vs -> v :: vs) set |>
  List.sort String.compare

(* Extract the signature from a set of clauses (steps). It suffices to use the
 * set of initial clauses, as derived clauses may contain no new information.
 *
 * NOTE: The same questions in clean_eigenvars about modularity and point of
 * extraction of this information are valid here. *)
let extract_sig steps =
  (* Hash tables for storage, without duplication. We assume correct scripts,
   * where all appearances of a symbol have the same arity. *)
  let atoms = Hashtbl.create 10 in
  let terms = Hashtbl.create 10 in
  let add table name arity =
    if not (Hashtbl.mem table name) then Hashtbl.add table name arity
  in
  let to_list table =
    let unordered = Hashtbl.fold (fun k v kvs -> (k, v) :: kvs) table [] in
    List.sort (fun (k1, _) (k2, _) -> String.compare k1 k2) unordered
  in
  (* Recursive traversal. *)
  let rec term_sig (Term(name, args) as term) =
    if not (is_var term) then begin
      add terms name (List.length args) ;
      List.iter term_sig args
    end
  in
  let atom_sig (Atom(name, args)) =
    add atoms name (List.length args) ;
    List.iter term_sig args
  in
  let literal_sig = function
    | Positive(atom) | Negative(atom) -> atom_sig atom
  in
  let step_sig (Step(_, clause, _)) =
    List.iter literal_sig clause
  in
  (* Extraction. *)
  List.iter step_sig steps ;
  (to_list atoms, to_list terms)

(* Printers for logical connectives. *)
let falsehood = "ff"

let neg body = Printf.sprintf "(ng %s)" body

let disj left right = Printf.sprintf "(or %s %s)" left right

(* Printers for certificate tactics. *)
let resolve src1 src2 dst =
  Printf.sprintf "resolve'' %d (res'' %d (rex'' %d done''))" dst src1 src2

let factor src dst =
  Printf.sprintf "factor'' %d %d" src dst

(* Printers for AST nodes. *)
let rec print_name_args name args = match args with
  | []     ->
      name
  | _ :: _ ->
      let args_str = args |> List.map print_term |> String.concat " " in
      Printf.sprintf "(%s %s)" name args_str
and print_term (Term(name, args)) =
  print_name_args name args

let print_atom (Atom(name, args)) =
  print_name_args name args

let print_literal = function
  | Positive(atom) -> print_atom atom
  | Negative(atom) -> neg (print_atom atom)

(* NOTE: Associativity of disjunction should not be a problem for the
 * certificate, but keep in mind in case of misbehavior. *)
let rec print_clause = function
  | []                  -> falsehood
  | [l]                 -> print_literal l
  | l :: (_ :: _ as ls) -> disj (print_literal l) (print_clause ls)

let print_quantified_clause clause = match clause_eigenvars clause with
  | [] ->
      print_clause clause
  | _ :: _ as vs ->
      let binder =
        vs |>
        List.map (fun v -> Printf.sprintf "forall %s\\" v)
        |> String.concat " "
      in
      Printf.sprintf "(%s %s)" binder (print_clause clause)

let print_clauses steps =
  steps |>
  List.map (fun (Step(_, clause, _)) -> print_quantified_clause clause) |>
  String.concat ",\n"

let print_tactic index (Step(dst, _, tactic)) =
  (* Index lookups are guaranteed to work if the proof script was properly
   * constructed. *)
  let find num = Hashtbl.find index num in
  match tactic with
  | Resolve(src1, src2)      -> resolve (find src1) (find src2) (find dst)
  | Factor(src) | Merge(src) -> factor (find src) (find dst)
  | Assumption | Clausify(_) -> assert false

let print_tactics initial derived =
  (* Renumber the N initial clauses to 1..N, and the M derived clauses to
   * N+1..N+M. *)
  let n_initial, n_derived = List.length initial, List.length derived in
  let index = Hashtbl.create (n_initial + n_derived) in
  let add (Step(olde, _, _)) newe = Hashtbl.add index olde newe in
  List.iteri (fun i s -> add s (i + 1)) initial ;
  List.iteri (fun i s -> add s (i + 1 + n_initial)) derived ;
  (* Translate the tactics based on the general scheme and this renumbering. *)
  derived |>
  List.map (print_tactic index) |>
  String.concat ",\n"

let print initial derived =
  Printf.sprintf "[\n%s\n]\n[\n%s\n]\n[\n%s\n]\n"
    (print_clauses initial)
    (print_clauses derived)
    (print_tactics initial derived)

(* Printers for signatures.
 *
 * NOTE: Some refactoring is possible here. *)
let rec print_sig_args = function (* NOTE: Maybe make this nicer. *)
  | 0            -> ""
  | n when n > 0 -> "i -> " ^ (print_sig_args (n - 1))
  | _            -> assert false

let mod_args arity =
  let rec aux = function
    | 0 ->
        []
    | n when n > 0 ->
        let name = "X" ^ (string_of_int n) in
        name :: (aux (n - 1))
    | _  ->
        assert false
  in List.rev(aux arity)

let print_sig_atom (name, arity) =
  Printf.sprintf "type   %s   %sbool." name (print_sig_args arity)

let print_sig_term (name, arity) =
  Printf.sprintf "type   %s   %si." name (print_sig_args arity)

type user_defined =
  | Atom
  | Term

let print_mod_clause user_type (name, arity) =
  (* Names of predicates by kind. For terms, cut to avoid eigenvariable case. *)
  let pname_pred, size_pred, size_cut = match user_type with
    | Atom -> "pred_pname", "size_bool", ""
    | Term -> "fun_pname",  "size_term", ", !"
  in
  (* List of arguments. *)
  let args = mod_args arity in
  (* Full instance of term: application of argument list to term name/head. *)
  let head_and_args = match args with
    | [] -> name
    | _ :: _ -> Printf.sprintf "(%s %s)" name (String.concat " " args)
  in
  (* List of size arguments. *)
  let size_args = List.map (fun arg -> "Size" ^ arg) args in
  (* List of recursive calls for size arguments. *)
  let size_term arg size_arg = Printf.sprintf "size_term %s %s" arg size_arg in
  let size_clauses = List.map2 size_term args size_args in
  (* In the body, concat parts and, if not null, and the final separator. *)
  let join sep strs =
    let colophon = if List.length strs > 0 then sep else "" in
    (String.concat sep strs) ^ colophon
  in
  (* Printers and OCaml types. *)
  let printer_clause = match user_type with (* TODO: Refactor. *)
    | Atom ->
        Printf.sprintf "print_name \"%s\" :- print \"%s\"."
          name (String.capitalize_ascii name)
    | Term ->
        let print_clauses =
          args |>
          List.map (fun x -> "print_term " ^ x ^ ", ") |>
          String.concat "print \", \", " in
        let print_block =
          if arity = 0 then ""
          else Printf.sprintf " print \"(\", %sprint \")\"," print_clauses
        in
        Printf.sprintf "print_term %s :- print \"%s\",%s !."
          head_and_args (String.capitalize_ascii name) print_block
  in
  let ocaml_clause = match user_type with (* TODO: Refactor. *)
    | Atom ->
        let of_args =
          let prefix = if arity = 0 then "" else " of " in
          let body = args |> List.map (fun _ -> "'a") |> String.concat " * " in
          prefix ^ body
        in
        Printf.sprintf "%%atom%%| %s%s" (String.capitalize_ascii name) of_args
    | Term ->
        let of_args =
          let prefix = if arity = 0 then "" else " of " in
          let body = args |> List.map (fun _ -> "t") |> String.concat " * " in
          prefix ^ body
        in
        Printf.sprintf "%%term%%| %s%s" (String.capitalize_ascii name) of_args
  in
  (* Code. As per [join] above, in the body only default values without
   * formatting are given, which is rather ugly. *)
  Printf.sprintf
    "%s %s \"%s\" [%s].\n\
     %s %s Size :- %sSize is %s1%s.\n\
     %s\n\
     %s"
    pname_pred head_and_args name (String.concat ", " args)
    size_pred head_and_args (join ", " size_clauses) (join " + " size_args)
      size_cut
    printer_clause
    ocaml_clause

let print_mod_atom atom =
  print_mod_clause Atom atom

let print_mod_term term =
  print_mod_clause Term term

let print_sig_atoms atoms =
  atoms |> List.map print_sig_atom |> String.concat "\n"

let print_sig_terms terms =
  terms |> List.map print_sig_term |> String.concat "\n"

let print_mod_atoms atoms =
  atoms |> List.map print_mod_atom |> String.concat "\n"

let print_mod_terms terms =
  terms |> List.map print_mod_term |> String.concat "\n"

let print_sig atoms terms =
  Printf.sprintf "%s\n%s\n" (print_sig_atoms atoms) (print_sig_terms terms)

let print_mod atoms terms =
  Printf.sprintf "%s\n%s\n" (print_mod_atoms atoms) (print_mod_terms terms)

(* AST processing entry point. *)
let process steps =
  let (initial, derived) = steps |> clean |> reorder in
  (* Signature. *)
  let (atoms, terms) = extract_sig initial in
  let signature = print_sig atoms terms in
  Printf.printf "%s%!" signature ;
  let mod_clauses = print_mod atoms terms in
  Printf.printf "%s%!" mod_clauses ;
  (* Certificate. *)
  let translation = print initial derived in
  Printf.printf "example 1\n%s.%!" translation

(* Main program. *)
let () =
  if Array.length Sys.argv = 2 then
    let filename = Sys.argv.(1) in
    let channel = open_in filename in
    let lexbuf = Lexing.from_channel channel in
    let ast = parse lexbuf in
    process ast
