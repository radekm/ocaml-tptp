(* Copyright (c) 2012-2013 Radek Micek *)

(** Reading and writing FOF and CNF formulas in TPTP format.

   Note 1: This library supports only FOF and CNF formulas.
   Keywords and other constructions used for representation
   of other formulas are not supported.
   This besides other things means that strings ["thf"],
   ["tff"], ["$thf"] and ["$tff"] are not treated as
   keywords and can be used as ordinary functors
   (for example [to_defined_word "$thf"] does not fail).

   Note 2: Comment lines can contain tabs. Comment blocks
   can contain non-printable characters and non-ASCII characters.

   Note 3: Comment blocks are ignored and comment lines inside formulas
   are ignored too.
*)

exception Input_closed

exception Parse_error of Lexing.position * string

type input

val create_in : Lexing.lexbuf -> input

(** Returns [None] when EOF is reached.

   Raises [Input_closed] when input was closed. Raises [Parse_error]
   when input contains syntax error.
*)
val read : input -> Tptp_ast.tptp_input option

val close_in : input -> unit

val write : Buffer.t -> Tptp_ast.tptp_input -> unit

val to_string : Tptp_ast.tptp_input -> string
