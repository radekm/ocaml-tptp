(* Copyright (c) 2012-2014 Radek Micek *)

exception Input_closed
exception Parse_error of Lexing.position * string
exception Include_error of Lexing.position * string

let _ =
  let print err p msg =
    let open Lexing in
    let s =
      Printf.sprintf
        "%s: file \"%s\", line %d, column %d: %s"
        err p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol) msg in
    Some s in
  let print_error = function
    | Parse_error (p, msg) -> print "Tptp.Parse_error" p msg
    | Include_error (p, msg) -> print "Tptp.Include_error" p msg
    | _ -> None in
  Printexc.register_printer print_error

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

module File = struct

  let with_dispose dispose f x =
    let result =
      try
        f x
      with
        | e -> dispose x; raise e in

    dispose x;
    result

  let with_file file f =
    with_dispose
      Pervasives.close_in
      (fun inchan ->
        let module L = Lexing in
        let lexbuf = L.from_channel inchan in
        let pos = { lexbuf.L.lex_curr_p with L.pos_fname = file } in
        lexbuf.L.lex_curr_p <- pos;
        with_dispose close_in f (create_in lexbuf))
      (open_in file)

  (* The position is filled by [iter]. *)
  exception Include_error_wo_pos of string

  (* Filtering of formulas from an included file
     based on a formula selection.
  *)
  module Filter = struct

    type t = {
      incl : Tptp_ast.tptp_input -> bool;
      (* Called for each TPTP input in the included file.
         Returns [true] iff the TPTP input should be included.
      *)
      eof : unit -> unit;
      (* Called after reading the included file. *)
    }

    (* Creates a filter for the formula selection. *)
    let of_selection = function
      | [] ->
          let incl = function
            | Tptp_ast.Include _ -> failwith "Unexpected include"
            | Tptp_ast.Comment _ -> false
            | Tptp_ast.Fof_anno _
            | Tptp_ast.Cnf_anno _ -> true in

          { incl; eof = (fun _ -> ()) }
      | sel ->
          let remaining = Hashtbl.create (List.length sel) in
          List.iter
            (fun name ->
              try
                let n = Hashtbl.find remaining name in
                Hashtbl.replace remaining name (n + 1)
              with
                | Not_found -> Hashtbl.add remaining name 1)
            sel;

          let incl = function
            (* Includes must be resolved. *)
            | Tptp_ast.Include _ -> failwith "Unexpected include"
            | Tptp_ast.Comment _ -> false
            | Tptp_ast.Fof_anno { Tptp_ast.af_name = name; _ }
            | Tptp_ast.Cnf_anno { Tptp_ast.af_name = name; _ } ->
                try
                  let n = Hashtbl.find remaining name in
                  if n > 0 then
                    let _ = Hashtbl.replace remaining name (n - 1) in
                    true
                  else
                    let msg =
                      Printf.sprintf
                        "Formula \"%s\" already included"
                        (Tptp_printer.show_formula_name name) in
                    raise (Include_error_wo_pos msg)
                with
                  | Not_found -> false in

          let eof () =
            Hashtbl.iter
              (fun name n ->
                if n > 0 then
                  let msg =
                    Printf.sprintf
                      "Formula \"%s\" not included"
                      (Tptp_printer.show_formula_name name) in
                  raise (Include_error_wo_pos msg))
              remaining in

          { incl; eof }

  end

  let (|>) x f = f x

  let find_included_file ?base_dir included_from file =
    let paths =
      if Filename.is_relative file then
        let dirs =
          Filename.dirname included_from ::
          (match base_dir with
            | None -> []
            | Some s -> [s]) in
        dirs
        |> List.map (fun d -> Filename.concat d file)
      else
        [file] in
    let can_include f = Sys.file_exists f && not (Sys.is_directory f) in
    try
      paths
      |> List.find can_include
    with
      | Not_found -> raise (Include_error_wo_pos "File not found")

  let rec iter ?base_dir f file =
    let rec loop input =
      match read input with
        | None -> ()
        | Some (Tptp_ast.Include (included, sel)) ->
            let included =
              find_included_file ?base_dir file (included :> string) in
            let filter = Filter.of_selection sel in
            let f tptp_input =
              if filter.Filter.incl tptp_input then f tptp_input in
            iter ?base_dir f included;
            filter.Filter.eof ();
            loop input
        | Some tptp_input ->
            f tptp_input;
            loop input in
    with_file
      file
      (fun input ->
        try
          loop input
        with
          | Include_error_wo_pos msg ->
              let p = input.in_lexbuf.Lexing.lex_curr_p in
              raise (Include_error (p, msg)))

  let read ?base_dir file =
    let xs = ref [] in
    iter ?base_dir (fun x -> xs := x :: !xs) file;
    List.rev !xs

  let write_channel ~rfrac ~width inputs out =
    List.iter
      (fun tptp_input ->
        PPrint.ToChannel.pretty rfrac width out
          (Tptp_printer.print_tptp_input tptp_input))
      inputs

  let write ?(rfrac = 1.) ?(width = 80) file inputs =
    with_dispose
      close_out
      (write_channel ~rfrac ~width inputs)
      (open_out file)
end
