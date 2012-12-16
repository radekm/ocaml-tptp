(* Copyright (c) 2012 Radek Micek *)

(** Lexer. *)

(** [token inside lexbuf] reads token from [lexbuf]. [inside] flag denotes
   whether we are inside formula and if so all comments will be skipped.
*)
val token : bool ref -> Lexing.lexbuf -> Parser.token
