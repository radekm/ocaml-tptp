(* Copyright (c) 2012-2014 Radek Micek *)

exception Input_closed
exception Parse_error of Lexing.position * string

let _ =
  let print_parse_error = function
    | Parse_error (p, msg) ->
        let open Lexing in
        let s =
          Printf.sprintf
            "Tptp.Parse_error: file \"%s\", line %d, column %d: %s"
            p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol) msg in
        Some s
    | _ -> None in
  Printexc.register_printer print_parse_error

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
    | Tptp_parser.Error ->
        raise (Parse_error (input.in_lexbuf.Lexing.lex_curr_p, "Syntax error"))

let close_in input = input.in_closed <- true

let write ?(rfrac = 1.) ?(width = 80) b tptp_input =
  PPrint.ToBuffer.pretty rfrac width b
    (Tptp_printer.print_tptp_input tptp_input)

let to_string tptp_input =
  let b = Buffer.create 100 in
  write b tptp_input;
  Buffer.contents b
