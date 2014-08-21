(* Copyright (c) 2012, 2014 Radek Micek *)

type tptp_input =
  | Fof_anno of fof_formula annotated_formula
  | Cnf_anno of cnf_formula annotated_formula
  | Include of file_name * formula_name list
  | Comment of comment_line

and 't annotated_formula = {
  af_name : formula_name;
  af_role : formula_role;
  af_formula : 't;
  af_annos : annotations option;
}

and annotations = {
  a_source : gterm;
  a_useful_info : gterm list;
}

and formula_role =
  | R_axiom
  | R_hypothesis
  | R_definition
  | R_assumption
  | R_lemma
  | R_theorem
  | R_corollary
  | R_conjecture
  | R_negated_conjecture
  | R_plain
  | R_fi_domain
  | R_fi_functors
  | R_fi_predicates
  | R_type
  | R_unknown

and fof_formula =
  | Sequent of formula list * formula list
  | Formula of formula

and formula =
  | Binop of binop * formula * formula
  | Not of formula
  | Quant of quant * var * formula
  | Atom of atom

and binop =
  | Equiv
  | Implies
  | Implies_rev
  | Xor
  | Nor
  | Nand
  | Or
  | And

and quant =
  | All
  | Exists

and cnf_formula =
  | Clause of literal list

and literal =
  | Lit of sign * atom

and sign =
  | Pos
  | Neg

and atom =
  | Equals of term * term
  | Pred of atomic_word * term list

and term =
  | Var of var
  | Func of atomic_word * term list
  | Number of Q.t
  | String of tptp_string

(* We have to distinguish '$foo' from $foo and '$$bar' from $$bar.
   Both '$foo' and '$$bar' will be parsed as Plain_word while $foo
   will be parsed as Defined_word and $$bar as System_word.
*)
and atomic_word =
  | Plain_word of plain_word
  | Defined_word of defined_word
  | System_word of system_word

and var = string

and plain_word = string

(* Keywords ($fof, $cnf, $fot) are not allowed. *)
and defined_word = string

and system_word = string

and tptp_string = string

and comment_line = string

(* We have to distinguish '2' from 2. *)
and formula_name =
  | N_word of plain_word
  | N_integer of Z.t

and file_name = plain_word

(* In TPTP:

   - Names of predicates, functions and constants:
       - atomic_word - lower_word / single_quoted
       - atomic_defined_word - dollar_word
       - atomic_system_word - dollar_dollar_word
   - Names of variables:
       - variable - upper_word
   - Names of formulas:
       - name - atomic_word / integer
   - File names:
       - file_name - single_quoted
*)

and gterm =
  | G_data of gdata
  | G_cons of gdata * gterm
  | G_list of gterm list

and gdata =
  | G_func of plain_word * gterm list
  | G_var of var
  | G_number of Q.t
  | G_string of tptp_string
  | G_formula of gformula

and gformula =
  | G_fof of fof_formula
  | G_cnf of cnf_formula
  | G_fot of term

let check_suffix skip cond str =
  for i = skip to String.length str - 1 do
    if not (cond str.[i]) then
      failwith "Invalid character"
  done;
  str

let is_alpha_num = function
  | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' -> true
  | _ -> false

let to_var str =
  if str = "" then
    failwith "Empty string";
  if str.[0] < 'A' || str.[0] > 'Z' then
    failwith "Invalid character";
  check_suffix 1 is_alpha_num str

let to_plain_word str =
  if str = "" then
    failwith "Empty string";
  check_suffix 0 (fun c -> c >= '\032' && c <= '\126') str

let to_defined_word str =
  if str = "$fof" || str = "$cnf" || str = "$fot" then
    failwith "String is keyword";
  if String.length str < 2 then
    failwith "Too short string";
  if str.[0] <> '$' || str.[1] < 'a' || str.[1] > 'z' then
    failwith "Invalid character";
  check_suffix 2 is_alpha_num str

let to_system_word str =
  if String.length str < 3 then
    failwith "Too short string";
  if str.[0] <> '$' || str.[1] <> '$' || str.[2] < 'a' || str.[2] > 'z' then
    failwith "Invalid character";
  check_suffix 3 is_alpha_num str

let to_tptp_string str =
  check_suffix 0 (fun c -> c >= '\032' && c <= '\126') str

let to_comment_line str =
  check_suffix 0 (fun c -> (c >= '\032' && c <= '\126') || c = '\t') str
