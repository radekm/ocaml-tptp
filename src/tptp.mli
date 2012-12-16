(* Copyright (c) 2012 Radek Micek *)

(** Friendly interface for reading TPTP format. *)

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
