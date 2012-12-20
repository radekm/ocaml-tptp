{

open Tptp_parser

(* Parses decimal number without exponent. *)
let parse_decimal_fraction (str : string) : Q.t =
  try
    let pos = String.index str '.' in
    let exp = pos + 1 - String.length str in
    let nodot =
      String.sub str 0 pos ^
      String.sub str (pos+1) (String.length str - pos - 1) in

    let num = Z.of_string nodot in
    let den = Z.pow (Z.of_int 10) (-exp) in

    Q.make num den
  with
    (* No decimal dot. *)
    | Not_found -> Q.of_string str

let parse_floating_point_number (str : string) : Q.t =
  try
    let pos = String.index (String.lowercase str) 'e' in
    let decimal_fraction = parse_decimal_fraction (String.sub str 0 pos) in
    let exp =
      let exp_str = String.sub str (pos+1) (String.length str - pos - 1) in
      Z.to_int (Z.of_string exp_str) in

    if exp < 0 then
      let c = Z.pow (Z.of_int 10) (-exp) in
      Q.div decimal_fraction (Q.of_bigint c)
    else
      let c = Z.pow (Z.of_int 10) exp in
      Q.mul decimal_fraction (Q.of_bigint c)
  with
    (* No exponent. *)
    | Not_found -> parse_decimal_fraction str
    (* Exponent cannot be converted to int. *)
    | Z.Overflow
    (* Exponent is min_int (opposite number is negative because it is again min_int
       but Z.pow needs non-negative number).
    *)
    | Invalid_argument _ -> failwith "Exponent out of range"

let unescape c str =
  let b = Buffer.create (String.length str) in
  let rec loop i =
    if i < String.length str then
      if str.[i] = '\\' then
        if i+1 < String.length str && (str.[i+1] = '\\' || str.[i+1] = c) then begin
          Buffer.add_char b str.[i+1];
          loop (i+2)
        end else
          failwith "Malformed escape sequence"
      else begin
        Buffer.add_char b str.[i];
        loop (i+1)
      end in

  loop 0;
  Buffer.contents b

let unescape_single_quoted : string -> string = unescape '\''
let unescape_distinct_object : string -> string = unescape '"'

}

let not_star_slash =
  ([^'\n' '\r' '*']* '*'+ [^'\n' '\r' '/' '*'])* [^'\n' '\r' '*']*
let non_empty_not_star_slash =
  (['*']+ [^'\n' '\r' '/' '*'] | [^'\n' '\r' '*']) not_star_slash

let newline = "\r\n" | "\n" | "\r"

let sq_char = ['\032'-'\038' '\040'-'\091' '\093'-'\126'] | ['\\']['\'' '\\']
let do_char = ['\032'-'\033' '\035'-'\091' '\093'-'\126'] | ['\\']['"' '\\']

let alpha_numeric = ['a'-'z' 'A'-'Z' '0'-'9' '_']
let lower_word = ['a'-'z'] alpha_numeric*
let upper_word = ['A'-'Z'] alpha_numeric*

let sign = ['+' '-']

let positive_decimal = ['1'-'9'] ['0'-'9']*
let decimal = "0" | positive_decimal

let unsigned_integer = decimal
let integer = sign? unsigned_integer

(* Comments inside formulas are ignored. *)
rule token inside = parse
  | "fof"
      { inside := true; FOF_KW }
  | "cnf"
      { inside := true; CNF_KW }
  | "include"
      { inside := true; INCLUDE_KW }
  | "$fof"
      { DOLLAR_FOF_KW }
  | "$cnf"
      { DOLLAR_CNF_KW }
  | "$fot"
      { DOLLAR_FOT_KW }
  | "("
      { LPAR }
  | ")"
      { RPAR }
  | ","
      { COMMA }
  | "."
      { inside := false; DOT }
  | "["
      { LBRKT }
  | "]"
      { RBRKT }
  | ":"
      { COLON }
  | "!"
      { EXCLAMATION }
  | "?"
      { QUESTION }
  | "~"
      { TILDE }
  | "&"
      { AMPERSAND }
  | "|"
      { VLINE }
  | "<=>"
      { LESS_EQUALS_GREATER }
  | "=>"
      { EQUALS_GREATER }
  | "<="
      { LESS_EQUALS }
  | "<~>"
      { LESS_TILDE_GREATER }
  | "~|"
      { TILDE_VLINE }
  | "~&"
      { TILDE_AMPERSAND }
  | "*"
      { STAR }
  | "+"
      { PLUS }
  | "-->"
      { DASH_DASH_GREATER }
  | "="
      { EQUALS }
  | "!="
      { EXCLAMATION_EQUALS }
  | "%" (['\t' '\032'-'\255']* as x)
      { if not !inside then COMMENT x else token inside lexbuf }
  | "/*"
      { skip_comment_block inside lexbuf }
  | "'" (sq_char+ as x) "'"
      { SINGLE_QUOTED (unescape_single_quoted x) }
  | "\"" (do_char* as x) "\""
      { DISTINCT_OBJECT (unescape_distinct_object x) }
  | "$" lower_word
      { DOLLAR_WORD (Lexing.lexeme lexbuf) }
  | "$$" lower_word
      { DOLLAR_DOLLAR_WORD (Lexing.lexeme lexbuf) }
  | upper_word
      { UPPER_WORD (Lexing.lexeme lexbuf) }
  | lower_word
      { LOWER_WORD (Lexing.lexeme lexbuf) }
  | integer
      { INTEGER (Z.of_string (Lexing.lexeme lexbuf)) }
  | sign? decimal '/' positive_decimal
      { RATIONAL (Q.of_string (Lexing.lexeme lexbuf)) }
  | sign? decimal '.' ['0'-'9']+
      { REAL (parse_decimal_fraction (Lexing.lexeme lexbuf)) }
  | sign? decimal ('.' ['0'-'9']+)? ['e' 'E'] integer
      { REAL (parse_floating_point_number (Lexing.lexeme lexbuf)) }
  | ['\t' ' ']+
      { token inside lexbuf }
  | newline
      { Lexing.new_line lexbuf; token inside lexbuf }
  | eof
      { EOF }

and skip_comment_block inside = parse
  | non_empty_not_star_slash
      { skip_comment_block inside lexbuf }
  | newline
      { Lexing.new_line lexbuf; skip_comment_block inside lexbuf }
  | '*'+ '/'
      { token inside lexbuf }
