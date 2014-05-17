(* Copyright (c) 2013-2014 Radek Micek *)

open Tptp_ast

module PP = PPrint

let (^^) = PP.(^^)

(* ************************************************************************ *)

let print_list ldelim rdelim sep items p =
  PP.string ldelim ^^
  PP.separate_map (PP.string sep) p items ^^
  PP.string rdelim

(* ************************************************************************ *)
(* Terminals *)

let show_var (s : var) = (s :> string)

let escape c str =
  let b = Buffer.create (String.length str) in
  let rec loop i =
    if i < String.length str then begin
      if str.[i] = '\\' || str.[i] = c then
        Buffer.add_char b '\\';
      Buffer.add_char b str.[i];
      loop (i+1)
    end in

  loop 0;
  Buffer.contents b

let show_plain_word (s : plain_word) =
  let is_alpha_num = function
    | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' -> true
    | _ -> false in
  let s = (s :> string) in
  let rec is_alpha_numeric i =
    (i >= String.length s) ||
    (is_alpha_num s.[i] && is_alpha_numeric (i+1)) in
  (* No quotes needed. *)
  if
    (* s is lower word. *)
    (s.[0] >= 'a' && s.[0] <= 'z') &&
    is_alpha_numeric 1 &&
    (* s isn't keyword. *)
    s <> "fof" &&
    s <> "cnf" &&
    s <> "include"
  then
    s
  else
    "'" ^ escape '\'' s ^ "'"

let show_defined_word (s : defined_word) = (s :> string)

let show_system_word (s : system_word) = (s :> string)

let show_tptp_string (s : tptp_string) =
  "\"" ^ escape '"' (s :> string) ^ "\""

let show_comment_line (s : comment_line) = (s :> string)

let show_formula_name = function
  | N_word s -> show_plain_word s
  | N_integer i -> Z.to_string i

let show_file_name (s : file_name) = "'" ^ escape '\'' (s :> string) ^ "'"

let show_number n =
  if Q.den n = Z.one
  then Z.to_string (Q.num n)
  else Q.to_string n

let show_atomic_word = function
  | Plain_word s -> show_plain_word s
  | Defined_word s -> show_defined_word s
  | System_word s -> show_system_word s

let show_formula_role = function
  | R_axiom -> "axiom"
  | R_hypothesis -> "hypothesis"
  | R_definition -> "definition"
  | R_assumption -> "assumption"
  | R_lemma -> "lemma"
  | R_theorem -> "theorem"
  | R_conjecture -> "conjecture"
  | R_negated_conjecture -> "negated_conjecture"
  | R_plain -> "plain"
  | R_fi_domain -> "fi_domain"
  | R_fi_functors -> "fi_functors"
  | R_fi_predicates -> "fi_predicates"
  | R_type -> "type"
  | R_unknown -> "unknown"

(* ************************************************************************ *)
(* Non-terminals *)

type formula_form =
  | F_unitary
  | F_or
  | F_and
  | F_any

let rec print_fof_formula = function
  | Sequent (fs, fs') ->
      print_list "[" "]" ", " fs (print_formula ~form:F_any) ^^
      PP.string " --> " ^^
      print_list "[" "]" ", " fs' (print_formula ~form:F_any)
  | Formula f ->
      print_formula ~form:F_any f

and print_formula ?(form = F_unitary) = function
  | Binop (op, f, f') ->
      let l =
        let form =
          match op with
            | Equiv | Implies | Implies_rev | Xor | Nor | Nand -> F_unitary
            | Or -> F_or
            | And -> F_and in
        print_formula ~form f in
      let r = print_formula f' in
      let wrap =
        match op, form with
          (* No parens around resulting formula. *)
          | Or, F_or | And, F_and | _, F_any -> (fun x -> x)
          | _, _ -> PP.parens in
      let op =
        match op with
          | Equiv -> "<=>"
          | Implies -> "=>"
          | Implies_rev -> "<="
          | Xor -> "<~>"
          | Nor -> "~|"
          | Nand -> "~&"
          | Or -> "|"
          | And -> "&" in
      wrap (PP.infix 2 1 (PP.string op) l r)
  | Not (Atom (Equals (l, r))) ->
      print_equals_fol Neg l r
  | Not f ->
      PP.tilde ^^
      print_formula f
  | Quant (q, _, _) as f ->
      (* [vars] - consecutive variables quantified by [q]. *)
      let vars, f =
        let rec group_vars xs = function
          | Quant (q', x, f) when q = q' -> group_vars (x :: xs) f
          | f -> (List.rev xs, f) in
        group_vars [] f in
      PP.char
        begin match q with
          | All -> '!'
          | Exists -> '?'
        end ^^
      print_list "[" "]" ", " vars (fun v -> PP.string (show_var v)) ^^
      PP.string " : " ^^
      print_formula f
  | Atom a ->
      print_atom a

and print_cnf_formula (Clause lits) =
  match lits with
    (* Empty clause. *)
    | [] -> PP.string "$false"
    | l :: ls ->
        List.fold_left
          (fun acc l -> PP.infix 2 1 (PP.char '|') acc (print_literal l))
          (print_literal l)
          ls

and print_literal = function
  | Lit (sign, Equals (l, r)) -> print_equals_fol sign l r
  | Lit (sign, atom) ->
      (match sign with
        | Pos -> PP.empty
        | Neg -> PP.tilde) ^^
      print_atom atom

(* Prints (negated) equality atom. *)
and print_equals_fol sign l r =
  print_term l ^^
  PP.space ^^
  (match sign with
    | Pos -> PP.empty
    | Neg -> PP.bang) ^^
  PP.string "= " ^^
  print_term r

and print_atom = function
  | Equals (l, r) ->
      print_equals_fol Pos l r
  | Pred (p, args) ->
      PP.string (show_atomic_word p) ^^
      begin match args with
        | [] -> PP.empty
        | _ -> print_list "(" ")" ", " args print_term
      end

and print_term = function
  | Var v -> PP.string (show_var v)
  | Func (f, args) ->
      PP.string (show_atomic_word f) ^^
      begin match args with
        | [] -> PP.empty
        | _ -> print_list "(" ")" ", " args print_term
      end
  | Number n -> PP.string (show_number n)
  | String s -> PP.string (show_tptp_string s)

let rec print_tptp_input node =
  let print_anno_formula kw name role formula print_formula annos =
    PP.string kw ^^
    PP.char '(' ^^
    PP.string (show_formula_name name) ^^
    PP.string ", " ^^
    PP.string (show_formula_role role) ^^
    PP.string ", " ^^
    print_formula formula ^^
    match annos with
      | None -> PP.string ")."
      | Some annos ->
          PP.string ", " ^^
          print_gterm annos.a_source ^^
          match annos.a_useful_info with
            | [] -> PP.string ")."
            | _ ->
                PP.string ", " ^^
                print_list "[" "]" ", " annos.a_useful_info print_gterm ^^
                PP.string ")." in
  begin match node with
    | Fof_anno f ->
        print_anno_formula "fof"
          f.af_name f.af_role f.af_formula print_fof_formula f.af_annos
    | Cnf_anno f ->
        print_anno_formula "cnf"
          f.af_name f.af_role f.af_formula print_cnf_formula f.af_annos
    | Include (file, names) ->
        PP.string "include(" ^^
        PP.string (show_file_name file) ^^
        begin match names with
          | [] -> PP.empty
          | _ ->
              PP.string ", " ^^
              print_list "[" "]" ", " names
                (fun n -> PP.string (show_formula_name n))
        end ^^
        PP.string ")."
    | Comment s ->
        PP.char '%' ^^
        PP.string (show_comment_line s)
  end ^^
  PP.hardline

and print_gterm = function
  | G_data d -> print_gdata d
  | G_cons (d, t) ->
      print_gdata d ^^
      PP.string " : " ^^
      print_gterm t
  | G_list ts -> print_list "[" "]" ", " ts print_gterm

and print_gdata = function
  | G_func (f, args) ->
      PP.string (show_plain_word f) ^^
      begin match args with
        | [] -> PP.empty
        | _ -> print_list "(" ")" ", " args print_gterm
      end
  | G_var v -> PP.string (show_var v)
  | G_number n -> PP.string (show_number n)
  | G_string s -> PP.string (show_tptp_string s)
  | G_formula f -> print_gformula f

and print_gformula = function
  | G_fof f ->
      PP.string "$fof(" ^^
      print_fof_formula f ^^
      PP.char ')'
  | G_cnf f ->
      PP.string "$cnf(" ^^
      print_cnf_formula f ^^
      PP.char ')'
  | G_fot t ->
      PP.string "$fot(" ^^
      print_term t ^^
      PP.char ')'
