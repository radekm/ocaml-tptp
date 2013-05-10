(* Copyright (c) 2013 Radek Micek *)

(** Printer. *)

(** {6 Printing non-terminals to buffer} *)

val print_tptp_input : Buffer.t -> Tptp_ast.tptp_input -> unit

val print_fof_formula : Buffer.t -> Tptp_ast.fof_formula -> unit

val print_formula : Buffer.t -> Tptp_ast.formula -> unit

val print_cnf_formula : Buffer.t -> Tptp_ast.cnf_formula -> unit

val print_literal : Buffer.t -> Tptp_ast.literal -> unit

val print_atom : Buffer.t -> Tptp_ast.atom -> unit

val print_term : Buffer.t -> Tptp_ast.term -> unit

val print_gterm : Buffer.t -> Tptp_ast.gterm -> unit

val print_gdata : Buffer.t -> Tptp_ast.gdata -> unit

val print_gformula : Buffer.t -> Tptp_ast.gformula -> unit

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
