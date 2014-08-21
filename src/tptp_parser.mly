/* Copyright (c) 2012 Radek Micek */

%{

open Tptp_ast

let string_to_role : string -> formula_role = function
  | "axiom" -> R_axiom
  | "hypothesis" -> R_hypothesis
  | "definition" -> R_definition
  | "assumption" -> R_assumption
  | "lemma" -> R_lemma
  | "theorem" -> R_theorem
  | "corollary" -> R_corollary
  | "conjecture" -> R_conjecture
  | "negated_conjecture" -> R_negated_conjecture
  | "plain" -> R_plain
  | "fi_domain" -> R_fi_domain
  | "fi_functors" -> R_fi_functors
  | "fi_predicates" -> R_fi_predicates
  | "type" -> R_type
  | "unknown" -> R_unknown
  | _ -> failwith "Unrecognized formula role"

let proc_literals = function
  | [ Lit (sign, Pred (Defined_word pred, [])) ]
    when (pred :> string) = "$false" -> []
  | lits -> List.rev lits

let term_to_atom : term -> atom = function
  | Func (pred, args) -> Pred (pred, args)
  | Var _
  | Number _
  | String _ -> failwith "Term cannot be converted to atom"

%}

/* Keywords */
%token FOF_KW CNF_KW INCLUDE_KW
%token DOLLAR_FOF_KW DOLLAR_CNF_KW DOLLAR_FOT_KW
/* Punctuation */
%token LPAR RPAR COMMA DOT LBRKT RBRKT COLON
/* Operators */
%token EXCLAMATION QUESTION TILDE AMPERSAND VLINE
%token LESS_EQUALS_GREATER EQUALS_GREATER LESS_EQUALS
%token LESS_TILDE_GREATER TILDE_VLINE TILDE_AMPERSAND STAR PLUS
%token DASH_DASH_GREATER
/* Predicates */
%token EQUALS EXCLAMATION_EQUALS

%token <string> COMMENT
%token <string> SINGLE_QUOTED
%token <string> DISTINCT_OBJECT
%token <string> DOLLAR_WORD
%token <string> DOLLAR_DOLLAR_WORD
%token <string> UPPER_WORD
%token <string> LOWER_WORD
%token <Z.t> INTEGER
%token <Q.t> RATIONAL
%token <Q.t> REAL

%token EOF

%start tptp_input
%type <Tptp_ast.tptp_input option> tptp_input

%%

tptp_input:
| annotated_formula
    { Some $1 }
| tptp_include
    { Some $1 }
| COMMENT
    { Some (Comment (to_comment_line $1)) }
| EOF
    { None }

annotated_formula:
| fof_annotated
    { $1 }
| cnf_annotated
    { $1 }

fof_annotated:
| FOF_KW LPAR name COMMA formula_role COMMA fof_formula annotations RPAR DOT
    { Fof_anno { af_name = $3; af_role = $5; af_formula = $7; af_annos = $8 } }

cnf_annotated:
| CNF_KW LPAR name COMMA formula_role COMMA cnf_formula annotations RPAR DOT
    { Cnf_anno { af_name = $3; af_role = $5; af_formula = $7; af_annos = $8 } }

annotations:
| COMMA source optional_info
    { Some { a_source = $2; a_useful_info = $3 } }
| null
    { None }

formula_role:
| LOWER_WORD
    { string_to_role $1 }

fof_formula:
| fof_logic_formula
    { Formula $1 }
| fof_sequent
    { $1 }

fof_logic_formula:
| fof_binary_formula
    { $1 }
| fof_unitary_formula
    { $1 }

fof_binary_formula:
| fof_binary_nonassoc
    { $1 }
| fof_binary_assoc
    { $1 }

fof_binary_nonassoc:
| fof_unitary_formula binary_connective fof_unitary_formula
    { Binop ($2, $1, $3) }

fof_binary_assoc:
| fof_or_formula
    { $1 }
| fof_and_formula
    { $1 }

fof_or_formula:
| fof_unitary_formula VLINE fof_unitary_formula
    { Binop (Or, $1, $3) }
| fof_or_formula VLINE fof_unitary_formula
    { Binop (Or, $1, $3) }

fof_and_formula:
| fof_unitary_formula AMPERSAND fof_unitary_formula
    { Binop (And, $1, $3) }
| fof_and_formula AMPERSAND fof_unitary_formula
    { Binop (And, $1, $3) }

fof_unitary_formula:
| fof_quantified_formula
    { $1 }
| fof_unary_formula
    { $1 }
| atomic_formula
    { Atom $1 }
| LPAR fof_logic_formula RPAR
    { $2 }

fof_quantified_formula:
| fol_quantifier LBRKT fof_variable_list RBRKT COLON fof_unitary_formula
    { List.fold_right (fun x f -> Quant ($1, x, f)) $3 $6 }

fof_variable_list:
| variable
    { [ $1 ] }
| variable COMMA fof_variable_list
    { $1 :: $3 }

fof_unary_formula:
| unary_connective fof_unitary_formula
    {
      (* The only one unary_connective is not. *)
      Not $2
    }
| fol_infix_unary
    {
      match $1 with
        | Pos, a -> Atom a
        | Neg, a -> Not (Atom a)
    }

fof_sequent:
| fof_tuple gentzen_arrow fof_tuple
    { Sequent ($1, $3) }
| LPAR fof_sequent RPAR
    { $2 }

fof_tuple:
| LBRKT RBRKT
    { [] }
| LBRKT fof_tuple_list RBRKT
    { $2 }

fof_tuple_list:
| fof_logic_formula
    { [ $1 ] }
| fof_logic_formula COMMA fof_tuple_list
    { $1 :: $3 }

cnf_formula:
| LPAR disjunction RPAR
    { Clause (proc_literals $2) }
| disjunction
    { Clause (proc_literals $1) }

disjunction:
| literal
    { [ $1 ] }
| disjunction VLINE literal
    { $3 :: $1 }

literal:
| atomic_formula
    { Lit (Pos, $1) }
| TILDE atomic_formula
    { Lit (Neg, $2) }
| fol_infix_unary
    { Lit (fst $1, snd $1) }

/* Returns tuple (sign, atom).
   Used by literal and fof_unary_formula.
*/
fol_infix_unary:
| term infix_inequality term
    { (Neg, Equals ($1, $3)) }

fol_quantifier:
| EXCLAMATION
    { All }
| QUESTION
    { Exists }

binary_connective:
| LESS_EQUALS_GREATER
    { Equiv }
| EQUALS_GREATER
    { Implies }
| LESS_EQUALS
    { Implies_rev }
| LESS_TILDE_GREATER
    { Xor }
| TILDE_VLINE
    { Nor }
| TILDE_AMPERSAND
    { Nand }

unary_connective:
| TILDE
    { }

gentzen_arrow:
| DASH_DASH_GREATER
    { }

atomic_formula:
| plain_atomic_formula
    { $1 }
| defined_atomic_formula
    { $1 }
| system_atomic_formula
    { $1 }

plain_atomic_formula:
| plain_term
    { term_to_atom $1 }

defined_atomic_formula:
| defined_plain_formula
    { term_to_atom $1 }
| defined_infix_formula
    { $1 }

defined_plain_formula:
| defined_plain_term
    { $1 }

defined_infix_formula:
| term defined_infix_pred term
    {
      (* The only one defined_infix_pred is equality. *)
      Equals ($1, $3)
    }

defined_infix_pred:
| infix_equality
    { }

infix_equality:
| EQUALS
    { }

infix_inequality:
| EXCLAMATION_EQUALS
    { }

system_atomic_formula:
| system_term
    { term_to_atom $1 }

term:
| function_term
    { $1 }
| variable
    { Var $1 }

function_term:
| plain_term
    { $1 }
| defined_term
    { $1 }
| system_term
    { $1 }

plain_term:
| constant
    { $1 }
| tptp_functor LPAR arguments RPAR
    { Func ($1, $3) }

constant:
| tptp_functor
    { Func ($1, []) }

tptp_functor:
| atomic_word
    { Plain_word $1  }

defined_term:
| defined_atom
    { $1 }
| defined_atomic_term
    { $1 }

defined_atom:
| number
    { Number $1 }
| DISTINCT_OBJECT
    { String (to_tptp_string $1) }

defined_atomic_term:
| defined_plain_term
    { $1 }

defined_plain_term:
| defined_constant
    { $1 }
| defined_functor LPAR arguments RPAR
    { Func ($1, $3) }

defined_constant:
| defined_functor
    { Func ($1, []) }

defined_functor:
| atomic_defined_word
    { Defined_word $1 }

system_term:
| system_constant
    { $1 }
| system_functor LPAR arguments RPAR
    { Func ($1, $3) }

system_constant:
| system_functor
    { Func ($1, []) }

system_functor:
| atomic_system_word
    { System_word $1 }

variable:
| UPPER_WORD
    { to_var $1 }

arguments:
| term
    { [ $1 ] }
| term COMMA arguments
    { $1 :: $3 }

source:
| general_term
    { $1 }

optional_info:
| COMMA useful_info
    { $2 }
| null
    { [] }

useful_info:
| general_list
    { $1 }

tptp_include:
| INCLUDE_KW LPAR file_name formula_selection RPAR DOT
    { Include ($3, $4) }

formula_selection:
| COMMA LBRKT name_list RBRKT
    { $3 }
| null
    { [] }

name_list:
| name
    { [ $1 ] }
| name COMMA name_list
    { $1 :: $3 }

general_term:
| general_data
    { G_data $1 }
| general_data COLON general_term
    { G_cons ($1, $3) }
| general_list
    { G_list $1 }

general_data:
| atomic_word
    { G_func ($1, []) }
| general_function
    { $1 }
| variable
    { G_var $1 }
| number
    { G_number $1 }
| DISTINCT_OBJECT
    { G_string (to_tptp_string $1) }
| formula_data
    { G_formula $1 }

general_function:
| atomic_word LPAR general_terms RPAR
    { G_func ($1, $3) }

formula_data:
| DOLLAR_FOF_KW LPAR fof_formula RPAR
    { G_fof $3 }
| DOLLAR_CNF_KW LPAR cnf_formula RPAR
    { G_cnf $3 }
| DOLLAR_FOT_KW LPAR term RPAR
    { G_fot $3 }

general_list:
| LBRKT RBRKT
    { [] }
| LBRKT general_terms RBRKT
    { $2 }

general_terms:
| general_term
    { [ $1 ] }
| general_term COMMA general_terms
    { $1 :: $3 }

name:
| atomic_word
    { N_word $1 }
| INTEGER
    { N_integer $1 }

atomic_word:
| LOWER_WORD
    { to_plain_word $1 }
| SINGLE_QUOTED
    { to_plain_word $1 }

atomic_defined_word:
| DOLLAR_WORD
    { to_defined_word $1 }

atomic_system_word:
| DOLLAR_DOLLAR_WORD
    { to_system_word $1 }

/* To ensure that same numbers written in different representations
   are equal we convert all numbers to Q.t.
*/
number:
| INTEGER
    { Q.of_bigint $1 }
| RATIONAL
    { $1 }
| REAL
    { $1 }

file_name:
| SINGLE_QUOTED
    { to_plain_word $1 }

null:
|
    { }
