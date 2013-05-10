(* Copyright (c) 2013 Radek Micek *)

open Tptp_ast

(* ************************************************************************ *)

let print_items b sep (items : 'a list) (p : Buffer.t -> 'a -> unit) =
  match items with
    | [] -> ()
    | x :: xs ->
        p b x;
        List.iter (fun a -> Buffer.add_string b sep; p b a) xs

let print_list b ldelim rdelim sep items p =
  Buffer.add_string b ldelim;
  print_items b sep items p;
  Buffer.add_string b rdelim

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

let rec print_fof_formula b = function
  | Sequent (fs, fs') ->
      print_list b "[" "]" ", " fs print_formula;
      Buffer.add_string b " --> ";
      print_list b "[" "]" ", " fs' print_formula
  | Formula f -> print_formula b f

(* TODO:
   - Reduce use of parentheses.
   - Group consecutive variables quantified by the same quantifier
     into one list.
*)
and print_formula b = function
  | Binop (op, f, f') ->
      Buffer.add_char b '(';
      print_formula b f;
      Buffer.add_string b ") ";
      Buffer.add_string b
        begin match op with
          | Equiv -> "<=>"
          | Implies -> "=>"
          | Implies_rev -> "<="
          | Xor -> "<~>"
          | Nor -> "~|"
          | Nand -> "~&"
          | Or -> "|"
          | And -> "&"
        end;
      Buffer.add_string b " (";
      print_formula b f';
      Buffer.add_char b ')'
  | Not (Atom (Equals (l, r))) ->
      print_equals_fol b Neg l r
  | Not f ->
      Buffer.add_string b "~(";
      print_formula b f;
      Buffer.add_char b ')'
  | Quant (q, v, f) ->
      Buffer.add_char b
        begin match q with
          | All -> '!'
          | Exists -> '?'
        end;
      Buffer.add_char b '[';
      Buffer.add_string b (show_var v);
      Buffer.add_string b "] : (";
      print_formula b f;
      Buffer.add_char b ')'
  | Atom a ->
      print_atom b a

and print_cnf_formula b (Clause lits) =
  print_list b "" "" " | " lits print_literal

and print_literal b = function
  | Lit (sign, Equals (l, r)) -> print_equals_fol b sign l r
  | Lit (sign, atom) ->
      if sign = Neg then
        Buffer.add_char b '~';
      print_atom b atom

(* Prints (negated) equality atom. *)
and print_equals_fol b sign l r =
  print_term b l;
  Buffer.add_char b ' ';
  if sign = Neg then
    Buffer.add_char b '!';
  Buffer.add_string b "= ";
  print_term b r

and print_atom b = function
  | Equals (l, r) ->
      print_equals_fol b Pos l r
  | Pred (p, args) ->
      Buffer.add_string b (show_atomic_word p);
      begin match args with
        | [] -> ()
        | _ -> print_list b "(" ")" ", " args print_term
      end

and print_term b = function
  | Var v -> Buffer.add_string b (show_var v)
  | Func (f, args) ->
      Buffer.add_string b (show_atomic_word f);
      begin match args with
        | [] -> ()
        | _ -> print_list b "(" ")" ", " args print_term
      end
  | Number n -> Buffer.add_string b (show_number n)
  | String s -> Buffer.add_string b (show_tptp_string s)

let rec print_tptp_input b node =
  let print_anno_formula kw name role formula print_formula annos =
    Buffer.add_string b kw;
    Buffer.add_char b '(';
    Buffer.add_string b (show_formula_name name);
    Buffer.add_string b ", ";
    Buffer.add_string b (show_formula_role role);
    Buffer.add_string b ", ";
    print_formula b formula;
    match annos with
      | None -> Buffer.add_string b ")."
      | Some annos ->
          Buffer.add_string b ", ";
          print_gterm b annos.a_source;
          match annos.a_useful_info with
            | [] -> Buffer.add_string b ")."
            | _ ->
                Buffer.add_string b ", ";
                print_list b "[" "]" ", " annos.a_useful_info print_gterm;
                Buffer.add_string b ")." in
  begin match node with
    | Fof_anno f ->
        print_anno_formula "fof"
          f.af_name f.af_role f.af_formula print_fof_formula f.af_annos
    | Cnf_anno f ->
        print_anno_formula "cnf"
          f.af_name f.af_role f.af_formula print_cnf_formula f.af_annos
    | Include (file, names) ->
        Buffer.add_string b "include(";
        Buffer.add_string b (show_file_name file);
        begin match names with
          | [] -> ()
          | _ ->
              Buffer.add_string b ", ";
              print_list b "[" "]" ", " names
                (fun b n -> Buffer.add_string b (show_formula_name n))
        end;
        Buffer.add_string b ")."
    | Comment s ->
        Buffer.add_char b '%';
        Buffer.add_string b (show_comment_line s)
  end;
  Buffer.add_char b '\n'

and print_gterm b = function
  | G_data d -> print_gdata b d
  | G_cons (d, t) ->
      print_gdata b d;
      Buffer.add_string b " : ";
      print_gterm b t
  | G_list ts -> print_list b "[" "]" ", " ts print_gterm

and print_gdata b = function
  | G_func (f, args) ->
      Buffer.add_string b (show_plain_word f);
      begin match args with
        | [] -> ()
        | _ -> print_list b "(" ")" ", " args print_gterm
      end
  | G_var v -> Buffer.add_string b (show_var v)
  | G_number n -> Buffer.add_string b (show_number n)
  | G_string s -> Buffer.add_string b (show_tptp_string s)
  | G_formula f -> print_gformula b f

and print_gformula b = function
  | G_fof f ->
      Buffer.add_string b "$fof(";
      print_fof_formula b f;
      Buffer.add_char b ')'
  | G_cnf f ->
      Buffer.add_string b "$cnf(";
      print_cnf_formula b f;
      Buffer.add_char b ')'
  | G_fot t ->
      Buffer.add_string b "$fot(";
      print_term b t;
      Buffer.add_char b ')'
