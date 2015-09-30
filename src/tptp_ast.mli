(* Copyright (c) 2012-2013, 2015 Radek Micek *)

(** AST for FOF and CNF formulas. *)

type tptp_input =
  | Fof_anno of fof_formula annotated_formula
  | Cnf_anno of cnf_formula annotated_formula
  | Include of file_name * formula_name list
  (** Empty list means that no selection was specified. *)
  | Comment of comment_line

and 't annotated_formula = {
  af_name : formula_name;
  af_role : formula_role;
  af_formula : 't;
  af_annos : annotations option;
}

(** Note: TPTP can distinguish between no useful info and empty useful info.
   But here are both represented by the empty list.
*)
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

(** Note: Type [atomic_word] has no equivalent in TPTP.
   Type [plain_word] correspons to [atomic_word] from TPTP.
*)
and atomic_word =
  | Plain_word of plain_word
  | Defined_word of defined_word
  | System_word of system_word

(** Alphanumeric characters include lowercase (['a'..'z'])
   and uppercase (['A'..'Z']) letters, digits (['0'..'9']) and underscore.
*)

(** Uppercase letter followed by zero or more alphanumeric characters.

   In TPTP: [variable].
*)
and var = private string

(** Nonempty string which consists of ASCII characters from space to tilde.

   In TPTP: [atomic_word].
*)
and plain_word = private string

(** Dollar followed by lowercase letter and zero or more alphanumeric
   characters. Keywords ([$fof], [$cnf], [$fot]) are not allowed.

   In TPTP: [atomic_defined_word].
*)
and defined_word = private string

(** Two dollars followed by lowercase letter and zero or more alphanumeric
   characters.

   In TPTP: [atomic_system_word].
*)
and system_word = private string

(** ASCII characters from space to tilde (empty string allowed).

   In TPTP: [distinct_object].
*)
and tptp_string = private string

(** Printable ASCII characters (code >= 32 && code <= 126)
   or tabs (empty string allowed).
*)
and comment_line = private string

(** In TPTP: [name]. *)
and formula_name =
  | N_word of plain_word
  | N_integer of Z.t

and file_name = plain_word

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

(** Raises [Failure] when the string is invalid. *)
val to_var : string -> var

(** Raises [Failure] when the string is invalid. *)
val to_plain_word : string -> plain_word

(** Raises [Failure] when the string is invalid. *)
val to_defined_word : string -> defined_word

(** Raises [Failure] when the string is invalid. *)
val to_system_word : string -> system_word

(** Raises [Failure] when the string is invalid. *)
val to_tptp_string : string -> tptp_string

(** Raises [Failure] when the string is invalid. *)
val to_comment_line : string -> comment_line

(** Useful when [(=)] causes stack overflow. *)
val tptp_input_equal : tptp_input -> tptp_input -> bool
