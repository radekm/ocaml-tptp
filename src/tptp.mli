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

exception Include_error of Lexing.position * string

type input

val create_in : Lexing.lexbuf -> input

(** Returns [None] when EOF is reached.

   Raises [Input_closed] when input was closed. Raises [Parse_error]
   when input contains syntax error.
*)
val read : input -> Tptp_ast.tptp_input option

val close_in : input -> unit

(** The parameter [width] is the maximum number of characters per line.
   The parameter [rfrac] is the ribbon width, a fraction relative to [width].
   The ribbon width is the maximum number of non-indentation characters
   per line.
*)
val write :
  ?rfrac:float -> ?width:int -> Buffer.t -> Tptp_ast.tptp_input -> unit

val to_string : Tptp_ast.tptp_input -> string

module File : sig
  (** Closes the file after the function terminates. *)
  val with_file : string -> (input -> 'a) -> 'a

  (** Reads TPTP inputs from the file. Includes are automatically resolved.

     Included files with a relative path are searched in the directory
     of the file they're included from, or if not found there
     then in [base_dir].

     Raises [Include_error] if an included file is not found.

     If an include is given without a formula selection then
     all formulas from the file are included.
     If an include is given with a formula selection
     then only selected formulas are included.

     If a formula selection contains [i] occurences of the name [n]
     then the included file must contain exactly [i] formulas
     with the name [n] otherwise [Include_error] is raised.
  *)
  val read : ?base_dir:string -> string -> Tptp_ast.tptp_input list

  (** Calls the function for each TPTP input in the file.

     Includes are treated the same way as in [read].
  *)
  val iter :
    ?base_dir:string -> (Tptp_ast.tptp_input -> unit) -> string -> unit

  (** [write file inputs] writes TPTP [inputs] to [file]. *)
  val write :
    ?rfrac:float -> ?width:int -> string -> Tptp_ast.tptp_input list -> unit
end
