(* Copyright (c) 2012, 2014-15 Radek Micek *)

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

(* ************************************************************************* *)
(* Equality *)

let rec list_equal eq xs ys k =
  match xs, ys with
    | x :: xs, y :: ys -> eq x y (fun () -> list_equal eq xs ys k)
    (* [(=)] won't cause stack overflow for the remaining cases. *)
    | _ -> xs = ys && k ()

let rec term_equal x x' k =
  match x, x' with
    | Func (f, args), Func (f', args') ->
        f = f' && list_equal term_equal args args' k
    (* [(=)] won't cause stack overflow for the remaining cases. *)
    | _ -> x = x' && k ()

let atom_equal x x' k =
  match x, x' with
    | Equals (l, r), Equals (l', r') ->
        term_equal l l' (fun () -> term_equal r r' k)
    | Pred (p, args), Pred (p', args') ->
        p = p' && list_equal term_equal args args' k
    | _ -> false

let literal_equal x x' k =
  match x, x' with
    | Lit (s, a), Lit (s', a') -> s = s' && atom_equal a a' k

let cnf_formula_equal x x' k =
  match x, x' with
    | Clause lits, Clause lits' -> list_equal literal_equal lits lits' k

let rec formula_equal x x' k =
  match x, x' with
    | Binop (op, l, r), Binop (op', l', r') ->
        op = op' && formula_equal l l' (fun () -> formula_equal r r' k)
    | Not f, Not f' -> formula_equal f f' k
    | Quant (q, x, f), Quant (q', x', f') ->
        q = q' && x = x' && formula_equal f f' k
    | Atom a, Atom a' -> atom_equal a a' k
    | _ -> false

let fof_formula_equal x x' k =
  match x, x' with
    | Sequent (xs, ys), Sequent (xs', ys') ->
        list_equal formula_equal xs xs' (fun () ->
        list_equal formula_equal ys ys' k)
    | Formula f, Formula f' -> formula_equal f f' k
    | _ -> false

let gformula_equal x x' k =
  match x, x' with
    | G_fof f, G_fof f' -> fof_formula_equal f f' k
    | G_cnf f, G_cnf f' -> cnf_formula_equal f f' k
    | G_fot t, G_fot t' -> term_equal t t' k
    | _ -> false

let rec gdata_equal x x' k =
  match x, x' with
    | G_func (f, args), G_func (f', args') ->
        f = f' && list_equal gterm_equal args args' k
    | G_formula f, G_formula f' -> gformula_equal f f' k
    (* [(=)] won't cause stack overflow for the remaining cases. *)
    | _ -> x = x' && k ()

and gterm_equal x x' k =
  match x, x' with
    | G_data d, G_data d' -> gdata_equal d d' k
    | G_cons (d, t), G_cons (d', t') ->
        gdata_equal d d' (fun () -> gterm_equal t t' k)
    | G_list ts, G_list ts' -> list_equal gterm_equal ts ts' k
    | _ -> false

let annotated_formula_equal eq x x' =
  x.af_name = x'.af_name &&
  x.af_role = x'.af_role &&
  eq x.af_formula x'.af_formula (fun () ->
  match x.af_annos, x'.af_annos with
    | Some a, Some a' ->
        gterm_equal a.a_source a'.a_source (fun () ->
        list_equal gterm_equal a.a_useful_info a'.a_useful_info (fun () ->
        true))
    (* [(=)] won't cause stack overflow for the remaining cases. *)
    | _ -> x.af_annos = x'.af_annos)

let tptp_input_equal x x' =
  match x, x' with
    | Fof_anno af, Fof_anno af' ->
        annotated_formula_equal fof_formula_equal af af'
    | Cnf_anno af, Cnf_anno af' ->
        annotated_formula_equal cnf_formula_equal af af'
    (* [(=)] won't cause stack overflow for the remaining cases. *)
    | _ -> x = x'
