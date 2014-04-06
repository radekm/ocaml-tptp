(* Copyright (c) 2012-2013 Radek Micek *)

exception Input_closed
exception Parse_error of Lexing.position * string

type input = {
  in_lexbuf : Lexing.lexbuf;
  in_inside : bool ref;
  mutable in_closed : bool;
}

let create_in lexbuf = {
  in_lexbuf = lexbuf;
  in_inside = ref false;
  in_closed = false;
}

let read input =
  if input.in_closed then
    raise Input_closed;
  try
    Tptp_parser.tptp_input (Tptp_lexer.token input.in_inside) input.in_lexbuf
  with
    | Failure s ->
        raise (Parse_error (input.in_lexbuf.Lexing.lex_curr_p, s))
    | Parsing.Parse_error ->
        raise (Parse_error (input.in_lexbuf.Lexing.lex_curr_p, "Syntax error"))

let close_in input = input.in_closed <- true

let write b tptp_input =
  PPrint.ToBuffer.pretty 1. 80 b (Tptp_printer.print_tptp_input tptp_input)
