(* Copyright (c) 2013 Radek Micek *)

(** Printer. *)

(** {6 Printing non-terminals to buffer} *)

val print_tptp_input : Tptp_ast.tptp_input -> PPrint.document

val print_fof_formula : Tptp_ast.fof_formula -> PPrint.document

val print_formula : ?unitary:bool -> Tptp_ast.formula -> PPrint.document

val print_cnf_formula : Tptp_ast.cnf_formula -> PPrint.document

val print_literal : Tptp_ast.literal -> PPrint.document

val print_atom : Tptp_ast.atom -> PPrint.document

val print_term : Tptp_ast.term -> PPrint.document

val print_gterm : Tptp_ast.gterm -> PPrint.document

val print_gdata : Tptp_ast.gdata -> PPrint.document

val print_gformula : Tptp_ast.gformula -> PPrint.document

(** {6 Writing terminals to string} *)

val show_formula_role : Tptp_ast.formula_role -> string

val show_atomic_word : Tptp_ast.atomic_word -> string

val show_var : Tptp_ast.var -> string

val show_plain_word : Tptp_ast.plain_word -> string

val show_defined_word : Tptp_ast.defined_word -> string

val show_system_word : Tptp_ast.system_word -> string

val show_tptp_string : Tptp_ast.tptp_string -> string

val show_comment_line : Tptp_ast.comment_line -> string

val show_formula_name : Tptp_ast.formula_name -> string

val show_file_name : Tptp_ast.file_name -> string
