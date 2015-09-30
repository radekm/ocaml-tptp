(* Copyright (c) 2012-2015 Radek Micek *)

open OUnit
open Tptp_ast

let data_dir = "data/"

let with_dispose dispose f x =
  let result =
    try
      f x
    with
      | e -> dispose x; raise e in

  dispose x;
  result

(* ************************************************************************* *)
(* Unit tests *)

let parse_lexbuf lexbuf =
  let rec loop acc input =
    try
      match Tptp.read input with
        | None -> List.rev acc, None
        | Some x -> loop (x::acc) input
    with
      | exn -> List.rev acc, Some exn in

  with_dispose Tptp.close_in (loop []) (Tptp.create_in lexbuf)

let parse_string str = parse_lexbuf (Lexing.from_string str)

let assert_parses ast str =
  let real_ast, real_exn = parse_string str in
  match real_exn with
    | None -> assert_equal ast real_ast
    | Some e -> raise e

let assert_parses_and_raises ast str =
  let real_ast, real_exn = parse_string str in
  match real_exn with
    | None -> assert_failure "No exception raised"
    | Some (Tptp.Parse_error (_, _)) -> assert_equal ast real_ast
    | Some e -> raise e

(* Uses [tptp_input_equal] instead of [(=)] to prevent [Out of memory]
   exception because of [Stack overflow in structural comparison].
*)
let assert_parses_deep ast str =
  let real_ast, real_exn = parse_string str in
  let rec cmp xs ys =
    match xs, ys with
      | x :: xs, y :: ys -> tptp_input_equal x y && cmp xs ys
      | _ -> xs = ys in
  match real_exn with
    | None -> assert_equal ~cmp ast real_ast
    | Some e -> raise e

let assert_raises_failure (f : unit -> 'a) : unit =
  let raised =
    try
      f ();
      false
    with Failure _ -> true in
  if not raised then
    assert_failure "Failure not raised"

let test_parse_fof1 () =
  let str = "fof(1, axiom, p(X))." in

  let p a = Pred (Plain_word (to_plain_word "p"), [a]) in
  let x = Var (to_var "X") in

  let ast = [
    Fof_anno {
      af_name = N_integer (Z.of_int 1);
      af_role = R_axiom;
      af_formula = Formula (Atom (p x));
      af_annos = None;
    };
  ] in

  assert_parses ast str

let test_parse_fof2 () =
  let str = "fof(2, axiom, p(c))." in

  let p a = Pred (Plain_word (to_plain_word "p"), [a]) in
  let c = Func (Plain_word (to_plain_word "c"), []) in

  let ast = [
    Fof_anno {
      af_name = N_integer (Z.of_int 2);
      af_role = R_axiom;
      af_formula = Formula (Atom (p c));
      af_annos = None;
    };
  ] in

  assert_parses ast str

let test_parse_fof3 () =
  let str = "fof(assoc, axiom, f(f(X, Y), Z) = f(X, f(Y, Z)))." in

  let f a b = Func (Plain_word (to_plain_word "f"), [a; b]) in
  let x = Var (to_var "X") in
  let y = Var (to_var "Y") in
  let z = Var (to_var "Z") in

  let ast = [
    Fof_anno {
      af_name = N_word (to_plain_word "assoc");
      af_role = R_axiom;
      af_formula = Formula (Atom (Equals (f (f x y) z, f x (f y z))));
      af_annos = None;
    };
  ] in

  assert_parses ast str

let test_parse_cnf () =
  let str = String.concat "" [
    "cnf(0, axiom, ~human(X) | mortal(X)).";
    "cnf(1, axiom, human(socrates)).";
    "cnf(2, negated_conjecture, ~mortal(socrates)).";
  ] in

  let human a = Pred (Plain_word (to_plain_word "human"), [a]) in
  let mortal a = Pred (Plain_word (to_plain_word "mortal"), [a]) in
  let socrates = Func (Plain_word (to_plain_word "socrates"), []) in
  let x = Var (to_var "X") in

  let ast = [
    Cnf_anno {
      af_name = N_integer (Z.of_int 0);
      af_role = R_axiom;
      af_formula = Clause [ Lit (Neg, human x); Lit (Pos, mortal x) ];
      af_annos = None;
    };
    Cnf_anno {
      af_name = N_integer (Z.of_int 1);
      af_role = R_axiom;
      af_formula = Clause [ Lit (Pos, human socrates) ];
      af_annos = None;
    };
    Cnf_anno {
      af_name = N_integer (Z.of_int 2);
      af_role = R_negated_conjecture;
      af_formula = Clause [ Lit (Neg, mortal socrates) ];
      af_annos = None;
    };
  ] in

  assert_parses ast str

let test_parse_include () =
  let str = "include('axioms02.tptp')." in

  let ast = [
    Include (to_plain_word "axioms02.tptp", []);
  ] in

  assert_parses ast str

let test_parse_include_with_formula_sel () =
  let str = "include('shared.tptp', [2, assoc, '2'])." in

  let ast = [
    Include (to_plain_word "shared.tptp", [
      N_integer (Z.of_int 2);
      N_word (to_plain_word "assoc");
      N_word (to_plain_word "2");
    ]);
  ] in

  assert_parses ast str

let test_reject_include_without_quotes () =
  let str = "include(axioms)." in
  assert_parses_and_raises [] str

let test_parse_integer () =
  let str = String.concat "" [
    "cnf(0, axiom, 0 != 1).";
    "cnf(1, lemma, f(-0, 0) = 0).";
    "cnf(2, lemma, f(17, 0) = +17).";
    "cnf(3, lemma, 0 = f(-13, 13)).";
  ] in

  let f a b = Func (Plain_word (to_plain_word "f"), [a; b]) in
  let num i = Number (Q.of_int i) in

  let ast = [
    Cnf_anno {
      af_name = N_integer (Z.of_int 0);
      af_role = R_axiom;
      af_formula = Clause [ Lit (Neg, Equals (num 0, num 1)) ];
      af_annos = None;
    };
    Cnf_anno {
      af_name = N_integer (Z.of_int 1);
      af_role = R_lemma;
      af_formula = Clause [ Lit (Pos, Equals (f (num 0) (num 0), num 0)) ];
      af_annos = None;
    };
    Cnf_anno {
      af_name = N_integer (Z.of_int 2);
      af_role = R_lemma;
      af_formula = Clause [ Lit (Pos, Equals (f (num 17) (num 0), num 17)) ];
      af_annos = None;
    };
    Cnf_anno {
      af_name = N_integer (Z.of_int 3);
      af_role = R_lemma;
      af_formula = Clause [ Lit (Pos, Equals (num 0, f (num ~-13) (num 13))) ];
      af_annos = None;
    };
  ] in

  assert_parses ast str

let test_parse_huge_integer () =
  let i = Z.pow (Z.of_int max_int) 12 in
  let str = "fof(" ^ Z.to_string i ^ ", axiom, p(" ^ Z.to_string i ^ "))." in

  let p a = Pred (Plain_word (to_plain_word "p"), [a]) in

  let ast = [
    Fof_anno {
      af_name = N_integer i;
      af_role = R_axiom;
      af_formula = Formula (Atom (p (Number (Q.of_bigint i))));
      af_annos = None;
    };
  ] in

  assert_parses ast str

(* Note: 02 is parsed as two integers 0 and 2. *)
let test_reject_integer_with_leading_zero () =
  let str = "cnf(02, axiom, p)." in
  assert_parses_and_raises [] str

let test_parse_rational () =
  let str = "fof(1, axiom, -5/3 = -15/9 & 3/4 != 4/3)." in

  let num i j = Number (Q.of_ints i j) in

  let ast = [
    Fof_anno {
      af_name = N_integer Z.one;
      af_role = R_axiom;
      af_formula =
        Formula (Binop (And,
          Atom (Equals (num ~-5 3, num ~-15 9)),
          Not (Atom (Equals (num 3 4, num 4 3)))));
      af_annos = None;
    };
  ] in

  assert_parses ast str

let test_reject_invalid_rational () =
  let str = "fof(1, axiom, -3/5 = 3/-5)." in
  assert_parses_and_raises [] str

let test_parse_real () =
  let str = "fof(-1, axiom, 1.2 = f(0.28, 0.92))." in

  let f a b = Func (Plain_word (to_plain_word "f"), [a; b]) in
  let num i j = Number (Q.of_ints i j) in

  let ast = [
    Fof_anno {
      af_name = N_integer Z.minus_one;
      af_role = R_axiom;
      af_formula = Formula (Atom (Equals (num 12 10, f (num 28 100) (num 92 100))));
      af_annos = None;
    };
  ] in

  assert_parses ast str

let test_reject_invalid_real () =
  let str = "cnf(1, axiom, 3.0 = 3.)." in
  assert_parses_and_raises [] str

let test_parse_real_with_exp () =
  let str = String.concat "" [
    "cnf(a, theorem, -37.2e-1 = -0.372e1).";
    "cnf(b, theorem, +372e-2 = 3.72e0).";
    "cnf(c, theorem, 0.0e+2 = 0).";
    "cnf(d, theorem, 0e+02 = 0).";
  ] in

  let x = Number (Q.of_ints ~-372 100) in
  let y = Number (Q.of_ints 372 100) in
  let z = Number Q.zero in

  let ast = [
    Cnf_anno {
      af_name = N_word (to_plain_word "a");
      af_role = R_theorem;
      af_formula = Clause [ Lit (Pos, Equals (x, x)) ];
      af_annos = None;
    };
    Cnf_anno {
      af_name = N_word (to_plain_word "b");
      af_role = R_theorem;
      af_formula = Clause [ Lit (Pos, Equals (y, y)) ];
      af_annos = None;
    };
    Cnf_anno {
      af_name = N_word (to_plain_word "c");
      af_role = R_theorem;
      af_formula = Clause [ Lit (Pos, Equals (z, z)) ];
      af_annos = None;
    };
    Cnf_anno {
      af_name = N_word (to_plain_word "d");
      af_role = R_theorem;
      af_formula = Clause [ Lit (Pos, Equals (z, z)) ];
      af_annos = None;
    };
  ] in

  assert_parses ast str

let test_parse_keyword_as_pred () =
  let str = "fof(0, axiom, cnf(X))." in

  let ast = [
    Fof_anno {
      af_name = N_integer Z.zero;
      af_role = R_axiom;
      af_formula =
        Formula
          (Atom (Pred (
            Plain_word (to_plain_word "cnf"),
            [Var (to_var "X")])));
      af_annos = None;
    };
  ] in

  assert_parses ast str

let test_parse_single_quoted () =
  let str = "cnf(' \\'hello world\\'', axiom, '\\\\')." in

  let ast = [
    Cnf_anno {
      af_name = N_word (to_plain_word " 'hello world'");
      af_role = R_axiom;
      af_formula = Clause [ Lit (Pos, Pred (Plain_word (to_plain_word "\\"), [])) ];
      af_annos = None;
    };
  ] in

  assert_parses ast str

let test_parse_single_quoted_with_kwds () =
  let str = "fof('fof', conjecture, '$fot' & 'include' & ~'cnf' & '$fof')." in

  let pred s = Pred (Plain_word (to_plain_word s), []) in

  let ast = [
    Fof_anno {
      af_name = N_word (to_plain_word "fof");
      af_role = R_conjecture;
      af_formula =
        Formula
          (List.fold_left
            (fun x y -> Binop (And, x, y))
            (Atom (pred "$fot"))
            [
              Atom (pred "include");
              Not (Atom (pred "cnf"));
              Atom (pred "$fof");
            ]
          );
      af_annos = None;
    };
  ] in

  assert_parses ast str

let test_reject_empty_single_quoted () =
  let str = "cnf('', axiom, p)." in
  assert_parses_and_raises [] str

let test_reject_single_quoted_inv_esc () =
  let str = "cnf('\\n', axiom, p)." in
  assert_parses_and_raises [] str

let test_reject_single_quoted_inv_char1 () =
  let str = "cnf('foo\127', axiom, p)." in
  assert_parses_and_raises [] str

let test_reject_single_quoted_inv_char2 () =
  let str = String.concat "" [
    "cnf('\032\126', axiom, p).";
    "cnf('\031bar', axiom, q).";
  ] in

  let ast = [
    Cnf_anno {
      af_name = N_word (to_plain_word "\032\126");
      af_role = R_axiom;
      af_formula = Clause [ Lit (Pos, Pred (Plain_word (to_plain_word "p"), [])) ];
      af_annos = None;
    };
  ] in

  assert_parses_and_raises ast str

let test_reject_unclosed_single_quoted () =
  let str = "cnf('hi" in
  assert_parses_and_raises [] str

let test_parse_distinct_object () =
  let str = String.concat "" [
    "fof(0, axiom, \"\\\\/\" != \"or\").";
    "fof(1, axiom, \"\\\"\" != \"double quote\").";
  ] in

  let or1 = String (to_tptp_string "\\/") in
  let or2 = String (to_tptp_string "or") in
  let dq1 = String (to_tptp_string "\"") in
  let dq2 = String (to_tptp_string "double quote") in

  let ast = [
    Fof_anno {
      af_name = N_integer Z.zero;
      af_role = R_axiom;
      af_formula = Formula (Not (Atom (Equals (or1, or2))));
      af_annos = None;
    };
    Fof_anno {
      af_name = N_integer Z.one;
      af_role = R_axiom;
      af_formula = Formula (Not (Atom (Equals (dq1, dq2))));
      af_annos = None;
    };
  ] in

  assert_parses ast str

let test_parse_empty_distinct_object () =
  let str = "cnf(10, axiom, empty(\"\"))." in

  let empty a = Pred (Plain_word (to_plain_word "empty"), [a]) in
  let empty_str = String (to_tptp_string "") in

  let ast = [
    Cnf_anno {
      af_name = N_integer (Z.of_int 10);
      af_role = R_axiom;
      af_formula = Clause [ Lit (Pos, empty empty_str) ];
      af_annos = None;
    };
  ] in

  assert_parses ast str

let test_parse_distinct_object_with_kwds () =
  let str =
    "cnf('$cnf', negated_conjecture, " ^
    "~p(\"$cnf\", \"fof\") | ~q(\"$fot\") | ~q(\"include\"))." in

  let p a b = Pred (Plain_word (to_plain_word "p"), [a; b]) in
  let q a = Pred (Plain_word (to_plain_word "q"), [a]) in

  let ast = [
    Cnf_anno {
      af_name = N_word (to_plain_word "$cnf");
      af_role = R_negated_conjecture;
      af_formula = Clause [
        Lit (Neg, p (String (to_tptp_string "$cnf")) (String (to_tptp_string "fof")));
        Lit (Neg, q (String (to_tptp_string "$fot")));
        Lit (Neg, q (String (to_tptp_string "include")));
      ];
      af_annos = None;
    };
  ] in

  assert_parses ast str

let test_reject_distinct_object_inv_char () =
  let str = "cnf(0, axiom, p(\"\000\"))." in
  assert_parses_and_raises [] str

let test_parse_var () =
  let str = "cnf(0, axiom, N = M | Hello = World)." in

  let ast = [
    Cnf_anno {
      af_name = N_integer Z.zero;
      af_role = R_axiom;
      af_formula = Clause [
        Lit (Pos, Equals (Var (to_var "N"), Var (to_var "M")));
        Lit (Pos, Equals (Var (to_var "Hello"), Var (to_var "World")));
      ];
      af_annos = None;
    };
  ] in

  assert_parses ast str

let test_parse_dollar_word () =
  let str = "fof(defined, axiom, $true <=> ~$false)." in

  let t = Pred (Defined_word (to_defined_word "$true"), []) in
  let f = Pred (Defined_word (to_defined_word "$false"), []) in

  let ast = [
    Fof_anno {
      af_name = N_word (to_plain_word "defined");
      af_role = R_axiom;
      af_formula = Formula (Binop (Equiv, Atom t, Not (Atom f)));
      af_annos = None;
    };
  ] in

  assert_parses ast str

let test_parse_dollar_dollar_word () =
  let str = "fof(0, axiom, $$foo(X))." in

  let foo a = Pred (System_word (to_system_word "$$foo"), [a]) in

  let ast = [
    Fof_anno {
      af_name = N_integer Z.zero;
      af_role = R_axiom;
      af_formula = Formula (Atom (foo (Var (to_var "X"))));
      af_annos = None;
    };
  ] in

  assert_parses ast str

let test_reject_invalid_dollar_word () =
  let str = "fof(0, axiom, $X)." in
  assert_parses_and_raises [] str

let test_reject_invalid_dollar_dollar_word () =
  let str = "fof(0, axiom, $$2)." in
  assert_parses_and_raises [] str

let test_parse_comment_line () =
  let str = String.concat ""
    [
      "%above\t1\n";
      "%above 2\r";
      "cnf(0, axiom, p). %middle\r\n";
      "%below 1\n";
      "%below 2"
    ] in

  let ast = [
    Comment (to_comment_line "above\t1");
    Comment (to_comment_line "above 2");
    Cnf_anno {
      af_name = N_integer Z.zero;
      af_role = R_axiom;
      af_formula = Clause [
        Lit (Pos, Pred (Plain_word (to_plain_word "p"), []));
      ];
      af_annos = None;
    };
    Comment (to_comment_line "middle");
    Comment (to_comment_line "below 1");
    Comment (to_comment_line "below 2");
  ] in

  assert_parses ast str

let test_inv_char_terminates_comment_line () =
  let str = "% hello \126\032\254" in
  let ast = [ Comment (to_comment_line " hello \126\032") ] in
  assert_parses_and_raises ast str

let test_skip_comment_line_inside_formula () =
  let str = "fof(0, axiom, % I'm inside formula\n p)." in

  let ast = [
    Fof_anno {
      af_name = N_integer Z.zero;
      af_role = R_axiom;
      af_formula = Formula (Atom (Pred (Plain_word (to_plain_word "p"), [])));
      af_annos = None;
    };
  ] in

  assert_parses ast str

let test_skip_comment_block () =
  let str = String.concat "" [
    "/* skip /* */";
    "cnf(0, /* skip \n skip */ axiom, p).";
    "  \t /* skip */ ";
  ] in

  let ast = [
    Cnf_anno {
      af_name = N_integer Z.zero;
      af_role = R_axiom;
      af_formula = Clause [
        Lit (Pos, Pred (Plain_word (to_plain_word "p"), []));
      ];
      af_annos = None;
    };
  ] in

  assert_parses ast str

let test_reject_unclosed_comment_block () =
  let str = "/* this is not closed" in
  assert_parses_and_raises [] str

let test_keywords_in_comments () =
  let str = String.concat "" [
    "/* % skip cnf $fof fof include \n";
    "*/ % cnf $fot $fof include $cnf\n";
    "% fof(0, axiom, p).\n";
  ] in

  let ast = [
    Comment (to_comment_line " cnf $fot $fof include $cnf");
    Comment (to_comment_line " fof(0, axiom, p).");
  ] in

  assert_parses ast str

let test_parse_annotations () =
  let str = String.concat "\n" [
    "fof(4,axiom,( ";
    "    ? [X3] : ";
    "      ( human(X3) ";
    "      & grade(X3) = a ) ), ";
    "    file('CreatedEqual.p',someone_got_an_a)). ";

    "fof(16,plain, ";
    "    ( human(esk1_0) ";
    "    & grade(esk1_0) = a ), ";
    "    inference(skolemize,[status(sab)],[4])). ";
  ] in

  let human t = Pred (Plain_word (to_plain_word "human"), [t]) in
  let grade t = Func (Plain_word (to_plain_word "grade"), [t]) in
  let x3' = to_var "X3" in
  let x3 = Var x3' in
  let a = Func (Plain_word (to_plain_word "a"), []) in
  let esk1_0 = Func (Plain_word (to_plain_word "esk1_0"), []) in

  let ast = [
    Fof_anno {
      af_name = N_integer (Z.of_int 4);
      af_role = R_axiom;
      af_formula =
        Formula (Quant (Exists, x3',
          Binop (And,
            Atom (human x3),
            Atom (Equals (grade x3, a)))));
      af_annos = Some {
        a_source = G_data (G_func ((to_plain_word "file"), [
          G_data (G_func (to_plain_word "CreatedEqual.p", []));
          G_data (G_func (to_plain_word "someone_got_an_a", []));
        ]));
        a_useful_info = [];
      };
    };
    Fof_anno {
      af_name = N_integer (Z.of_int 16);
      af_role = R_plain;
      af_formula =
        Formula (Binop (And,
          Atom (human esk1_0),
          Atom (Equals (grade esk1_0, a))));
      af_annos = Some {
        a_source = G_data (G_func ((to_plain_word "inference"), [
          G_data (G_func (to_plain_word "skolemize", []));
          G_list [G_data (G_func (to_plain_word "status",
            [G_data (G_func (to_plain_word "sab", []))]))
          ];
          G_list [G_data (G_number (Q.of_int 4))];
        ]));
        a_useful_info = [];
      };
    };
  ] in

  assert_parses ast str

let test_to_var_rejects_invalid_str () =
  assert_raises_failure (fun () ->
    to_var "");
  assert_raises_failure (fun () ->
    to_var "x");
  assert_raises_failure (fun () ->
    to_var "_X");
  assert_raises_failure (fun () ->
    to_var "123");
  assert_raises_failure (fun () ->
    to_var "X-Y");
  assert_raises_failure (fun () ->
    to_var "$foo")

let test_to_plain_word_rejects_invalid_str () =
  assert_raises_failure (fun () ->
    to_plain_word "");
  assert_raises_failure (fun () ->
    to_plain_word "\n");
  assert_raises_failure (fun () ->
    to_plain_word "foo\144");
  assert_raises_failure (fun () ->
    to_plain_word "hello\tworld")

let test_to_defined_word_rejects_invalid_str () =
  assert_raises_failure (fun () ->
    to_defined_word "");
  assert_raises_failure (fun () ->
    to_defined_word "a");
  assert_raises_failure (fun () ->
    to_defined_word "$");
  assert_raises_failure (fun () ->
    to_defined_word "A");
  assert_raises_failure (fun () ->
    to_defined_word "$A");
  assert_raises_failure (fun () ->
    to_defined_word "$$a");
  assert_raises_failure (fun () ->
    to_defined_word "$_a")

let test_to_system_word_rejects_invalid_str () =
  assert_raises_failure (fun () ->
    to_system_word "");
  assert_raises_failure (fun () ->
    to_system_word "$");
  assert_raises_failure (fun () ->
    to_system_word "$$");
  assert_raises_failure (fun () ->
    to_system_word "$$A");
  assert_raises_failure (fun () ->
    to_system_word "$$$a");
  assert_raises_failure (fun () ->
    to_system_word "a")

let test_to_tptp_string_rejects_invalid_str () =
  assert_raises_failure (fun () ->
    to_tptp_string "\031");
  assert_raises_failure (fun () ->
    to_tptp_string "hello\255");
  assert_raises_failure (fun () ->
    to_tptp_string "\n");
  assert_raises_failure (fun () ->
    to_tptp_string "\t");
  assert_raises_failure (fun () ->
    to_tptp_string "\r")

let test_to_comment_line_rejects_invalid_str () =
  assert_raises_failure (fun () ->
    to_comment_line "\n");
  assert_raises_failure (fun () ->
    to_comment_line "\r");
  assert_raises_failure (fun () ->
    to_comment_line "\000");
  assert_raises_failure (fun () ->
    to_comment_line "\127");
  assert_raises_failure (fun () ->
    to_comment_line "\255");
  assert_raises_failure (fun () ->
    to_comment_line "\031")

let test_print_cnf () =
  let ast =
    let p = Pred (Plain_word (to_plain_word "p"), []) in
    let q a b = Pred (Plain_word (to_plain_word "q"), [a; b]) in
    let fof a = Func (Plain_word (to_plain_word "fof"), [a]) in
    let c = Func (Plain_word (to_plain_word "c"), []) in
    let x = Var (to_var "X") in
    let y = Var (to_var "Y") in
    Cnf_anno {
      af_name = N_word (to_plain_word "foo_bar");
      af_role = R_negated_conjecture;
      af_formula = Clause [
        Lit (Pos, p);
        Lit (Neg, Equals (fof x, c));
        Lit (Neg, q x y);
        Lit (Pos, Equals (y, x));
      ];
      af_annos = None;
    } in

  let str =
    let f = "p | fof(X) != c | ~q(X, Y) | Y = X" in
    "cnf(foo_bar, negated_conjecture, " ^ f ^ ").\n" in

  assert_equal str (Tptp.to_string ast)

let test_tptp_input_equal () =
  let parse_single str =
    match parse_string str with
      | [ast], None -> ast
      | _ -> failwith "parse_single" in
  let ast1 = parse_single "fof(comm, axiom, p | f(X, Y) = f(Y, X))." in
  let ast2 = parse_single "fof(comm, axiom, p | f(X, Y) = f(Z, X))." in
  assert_equal (tptp_input_equal ast1 ast2) false

(* Pretty-printing and parsing should be tail-recursive. *)
let test_deep_term () =
  let term =
    let f a = Func (Plain_word (to_plain_word "f"), [a]) in
    let x = Var (to_var "X") in
    let t = ref x in
    for i = 1 to 10_000_000 do
      t := f !t
    done;
    !t in
  let atom = Pred (Plain_word (to_plain_word "p"), [term]) in
  let ast =
    Fof_anno {
      af_name = N_word (to_plain_word "deep");
      af_role = R_axiom;
      af_formula = Formula (Atom atom);
      af_annos = None;
    } in
  let str = Tptp.to_string ast in
  (* [assert_parses] isn't sufficient. *)
  assert_parses_deep [ast] str

let test_deep_fof () =
  let atom = Atom (Pred (Plain_word (to_plain_word "p"), [])) in
  let build ~depth op =
    let f = ref atom in
    for i = 1 to depth do
      f := op !f
    done;
    Fof_anno {
      af_name = N_word (to_plain_word "deep");
      af_role = R_axiom;
      af_formula = Formula !f;
      af_annos = None;
    } in
  let test ~depth op =
    let ast = build ~depth op in
    let str = Tptp.to_string ast in
    assert_parses_deep [ast] str in
  (* Unary connective. *)
  test ~depth:10_000_000 (fun f -> Not f);
  (* Binary connective, left-associated.

     Note: [assert_parses] isn't sufficient.
  *)
  test ~depth:10_000_000 (fun f -> Binop (And, f, atom));
  (* Binary connective, right-associated.

     Note: Depth is not [10_000_000] since the length
     of the pretty-printed right-associated formula
     is asymptotically quadratic. The reason is
     that the [i]-th line is indented by [2*i] spaces.
  *)
  test ~depth:40_000 (fun f -> Binop (And, atom, f));
  (* Single quantifier. *)
  test ~depth:10_000_000 (fun f -> Quant (All, to_var "X", f));
  (* Alternating quantifiers. *)
  test ~depth:10_000_000
    (let q = ref All in
     fun f ->
       q :=
         (match !q with
           | All -> Exists
           | Exists -> All);
       Quant (!q, to_var "X", f))

let test_deep_cnf () =
  let atom = Pred (Plain_word (to_plain_word "p"), []) in
  let clause =
    let lits = ref [] in
    for i = 1 to 10_000_000 do
      lits := Lit (Pos, atom) :: !lits
    done;
    Clause !lits in
  let ast =
    Cnf_anno {
      af_name = N_word (to_plain_word "deep");
      af_role = R_axiom;
      af_formula = clause;
      af_annos = None;
    } in
  let str = Tptp.to_string ast in
  assert_parses [ast] str

let test_deep_gterm () =
  let gterm =
    let gterm = ref (G_data (G_var (to_var "Y"))) in
    let f = to_plain_word "f" in
    for i = 1 to 10_000_000 do
      gterm := G_data (G_func (f, [G_data (G_var (to_var "X")); !gterm]))
    done;
    !gterm in
  let ast =
    Cnf_anno {
      af_name = N_word (to_plain_word "deep");
      af_role = R_axiom;
      af_formula = Clause [];
      af_annos = Some { a_source = gterm; a_useful_info = [] };
    } in
  let str = Tptp.to_string ast in
  (* [assert_parses] isn't sufficient. *)
  assert_parses_deep [ast] str

let test_read_file_with_includes () =
  let ast = Tptp.File.read (data_dir ^ "basic.exp") in
  let real_ast =
    Tptp.File.read
      ~base_dir:(data_dir ^ "basic/base-dir")
      (data_dir ^ "basic.in") in
  assert_equal ast real_ast

let test_read_file_included_file_not_found () =
  let file = data_dir ^ "file-not-found.in" in
  let pos =
    let open Lexing in
    { pos_fname = file; pos_lnum = 2; pos_bol = 37; pos_cnum = 70 } in
  assert_raises
    (Tptp.Include_error (pos, "File not found"))
    (fun () -> Tptp.File.read file)

let test_read_file_formula_not_included () =
  let file = data_dir ^ "formula-not-included.in" in
  let pos =
    let open Lexing in
    { pos_fname = file; pos_lnum = 2; pos_bol = 37; pos_cnum = 81 } in
  assert_raises
    (Tptp.Include_error (pos, "Formula \"b\" not included"))
    (fun () -> Tptp.File.read file)

let test_read_file_formula_already_included () =
  let pos =
    let open Lexing in
    let pos_fname = data_dir ^ "formula-already-included/a.tptp" in
    { pos_fname; pos_lnum = 2; pos_bol = 18; pos_cnum = 36 } in
  let file = data_dir ^ "formula-already-included.in" in
  assert_raises
    (Tptp.Include_error (pos, "Formula \"a\" already included"))
    (fun () -> Tptp.File.read file)

let test_write_file () =
  let ast = Tptp.File.read (data_dir ^ "basic.exp") in
  let tmp = Filename.temp_file "ocaml-tptp-test" "" in
  Tptp.File.write tmp ast;
  let real_ast = Tptp.File.read tmp in
  Sys.remove tmp;
  assert_equal ast real_ast

let suite =
  "suite" >:::
    [
      "parse FOF 1" >:: test_parse_fof1;
      "parse FOF 2" >:: test_parse_fof2;
      "parse FOF 3" >:: test_parse_fof3;
      "parse CNF" >:: test_parse_cnf;
      "parse include" >:: test_parse_include;
      "parse include with formula selection" >:: test_parse_include_with_formula_sel;
      "reject include without quotes" >:: test_reject_include_without_quotes;
      "parse integer" >:: test_parse_integer;
      "parse huge integer" >:: test_parse_huge_integer;
      "reject integer with leading zero" >:: test_reject_integer_with_leading_zero;
      "parse rational" >:: test_parse_rational;
      "reject invalid rational" >:: test_reject_invalid_rational;
      "parse real" >:: test_parse_real;
      "reject invalid real" >:: test_reject_invalid_real;
      "parse real with exponent" >:: test_parse_real_with_exp;
      "parse keyword as predicate" >:: test_parse_keyword_as_pred;
      "parse single-quoted" >:: test_parse_single_quoted;
      "parse single-quoted with keywords" >:: test_parse_single_quoted_with_kwds;
      "reject empty single-quoted" >:: test_reject_empty_single_quoted;
      "reject single-quoted with invalid escape sequence" >::
        test_reject_single_quoted_inv_esc;
      "reject single-quoted with invalid char 1" >::
        test_reject_single_quoted_inv_char1;
      "reject single-quoted with invalid char 2" >::
        test_reject_single_quoted_inv_char2;
      "reject unclosed single-quoted" >:: test_reject_unclosed_single_quoted;
      "parse distinct object" >:: test_parse_distinct_object;
      "parse empty distinct object" >:: test_parse_empty_distinct_object;
      "parse distinct object with keywords" >:: test_parse_distinct_object_with_kwds;
      "reject distinct object with invalid character" >::
        test_reject_distinct_object_inv_char;
      "parse var" >:: test_parse_var;
      "parse dollar word" >:: test_parse_dollar_word;
      "parse dollar dollar word" >:: test_parse_dollar_dollar_word;
      "reject invalid dollar word" >:: test_reject_invalid_dollar_word;
      "reject invalid dollar dollar word" >::
        test_reject_invalid_dollar_dollar_word;
      "parse comment line" >:: test_parse_comment_line;
      "invalid character terminates comment line" >::
        test_inv_char_terminates_comment_line;
      "skip comment line inside formula" >::
        test_skip_comment_line_inside_formula;
      "skip comment block" >::
        test_skip_comment_block;
      "reject unclosed comment block" >::
        test_reject_unclosed_comment_block;
      "keywords in comments" >:: test_keywords_in_comments;
      "parse annotations" >:: test_parse_annotations;
      "to_var rejects invalid string" >::
        test_to_var_rejects_invalid_str;
      "to_plain_word rejects invalid string" >::
        test_to_plain_word_rejects_invalid_str;
      "to_defined_word rejects invalid string" >::
        test_to_defined_word_rejects_invalid_str;
      "to_system_word rejects invalid string" >::
        test_to_system_word_rejects_invalid_str;
      "to_tptp_string rejects invalid string" >::
        test_to_tptp_string_rejects_invalid_str;
      "to_comment_line rejects invalid string" >::
        test_to_comment_line_rejects_invalid_str;
      "print CNF" >:: test_print_cnf;
      "tptp_input_equal" >:: test_tptp_input_equal;
      "deep term" >:: test_deep_term;
      "deep FOF" >:: test_deep_fof;
      "deep CNF" >:: test_deep_cnf;
      "deep gterm" >:: test_deep_gterm;
      "read file with includes" >:: test_read_file_with_includes;
      "read file - included file not found" >::
        test_read_file_included_file_not_found;
      "read file - formula not included" >::
        test_read_file_formula_not_included;
      "read file - formula already included" >::
        test_read_file_formula_already_included;
      "write file" >:: test_write_file;
    ]

(* ************************************************************************* *)
(* Parsing TPTP problems in given directory *)

exception Line_found

let exists_line f file =
  let rec test_lines in_chan : unit =
    if f (input_line in_chan) then
      raise Line_found
    else
      test_lines in_chan in

  try
    with_dispose close_in test_lines (open_in file);
    failwith "Unreachable"
  with
    | End_of_file -> false
    | Line_found -> true

let is_prefix_of pref str =
  let pref_len = String.length pref in
  let str_len = String.length str in
  str_len >= pref_len &&
  String.sub str 0 pref_len = pref

exception Tptp_input_not_preserved

let parse_tptp_problem file =
  let rec parse_all acc input =
    match Tptp.read input with
      | None -> List.rev acc
      | Some item ->
          parse_all (item :: acc) input in

  (* Read items from file. *)
  let items =
    with_dispose
      close_in
      (fun in_chan ->
        with_dispose
          Tptp.close_in
          (parse_all [])
          begin
            let module L = Lexing in
            let lexbuf = L.from_channel in_chan in
            let pos = { lexbuf.L.lex_curr_p with L.pos_fname = file } in
            lexbuf.L.lex_curr_p <- pos;
            Tptp.create_in lexbuf
          end)
      (open_in file) in

  (* Write items to string. *)
  let buf = Buffer.create 1024 in
  List.iter (Tptp.write buf) items;
  let str = Buffer.contents buf in
  Buffer.reset buf;

  (* Read items from string. *)
  let items' =
    with_dispose
      Tptp.close_in
      (parse_all [])
      (Tptp.create_in (Lexing.from_string str)) in

  if items <> items' then
    raise Tptp_input_not_preserved

(* Parses all files in given directory and its subdirectories
   which don't contain line starting with "thf(" or "tff(".

   Progress is reported to standard output.
*)
let parse_tptp_problems dir =
  let nparsed = ref 0 in
  let nfailed = ref 0 in
  let nskipped = ref 0 in

  let thf_or_tff_file =
    exists_line (fun ln -> is_prefix_of "thf(" ln || is_prefix_of "tff(" ln) in

  let rec parse_dir dir =
    let items = Sys.readdir dir in
    Array.iter (fun i ->
      let i = Filename.concat dir i in
      if Sys.is_directory i then
        parse_dir i
      else if thf_or_tff_file i then begin
        incr nskipped;
        print_string "S";
        flush stdout
      end else begin
        try
          parse_tptp_problem i;
          incr nparsed;
          print_string ".";
          flush stdout
        with
          | Tptp.Parse_error _ as e ->
              incr nfailed;
              Printf.printf "\n%s: %s\n" i (Printexc.to_string e);
              flush stdout
          | Tptp_input_not_preserved ->
              incr nfailed;
              Printf.printf "\n%s: %s\n" i "input not preserved";
              flush stdout
      end) items in

  parse_dir dir;

  print_newline ();
  Printf.printf "Parsed %d problems\n" !nparsed;
  Printf.printf "Failed %d problems\n" !nfailed;
  Printf.printf "Skipped %d problems\n" !nskipped

(* ************************************************************************* *)
(* Parsing TPTP problems in given directory with included files *)

let parse_tptp_problem_inc base_dir file =
  Tptp.File.iter ?base_dir ignore file

let parse_tptp_problems_inc base_dir dir =
  let nparsed = ref 0 in
  let nparse_errors = ref 0 in
  let nother_errors = ref 0 in

  let rec parse_dir dir =
    let items = Sys.readdir dir in
    Array.iter (fun i ->
      let i = Filename.concat dir i in
      if Sys.is_directory i then
        parse_dir i
      else begin
        try
          parse_tptp_problem_inc base_dir i;
          incr nparsed;
          print_string ".";
          flush stdout
        with
          | Tptp.Parse_error _ ->
              incr nparse_errors;
              print_string "P";
              flush stdout
          | e ->
              incr nother_errors;
              Printf.printf "\n%s: %s\n" i (Printexc.to_string e);
              flush stdout
      end) items in

  parse_dir dir;

  print_newline ();
  Printf.printf "Parsed %d problems\n" !nparsed;
  Printf.printf
    "Parse errors %d (expected for THF and TFF problems)\n" !nparse_errors;
  Printf.printf "Other errors %d\n" !nother_errors

(* ************************************************************************* *)
(* Parsing TPTP input from string *)

let parse_tptp_string str =
  let asts, exn = parse_string str in
  match exn with
    | Some e ->
        Printf.printf "Exception raised: %s\n" (Printexc.to_string e)
    | None ->
        (* Pretty-print parsed input. *)
        let str2 =
          let buf = Buffer.create 1024 in
          List.iter (Tptp.write ~width:20 buf) asts;
          Buffer.contents buf in

        Printf.printf "Parsed %d inputs:\n%s\n" (List.length asts) str2;

        (* Parse after pretty-printing. *)
        match parse_string str2 with
          | asts2, None ->
              if asts = asts2 then
                print_endline "Pretty-printing preserves input"
              else
                print_endline "Input is not preserved by pretty-printing"
          | _, Some e ->
              Printf.printf
                "Exception raised when parsing after pretty-printing: %s\n"
                (Printexc.to_string e)

(* ************************************************************************* *)
(* Main *)

let () =
  let base_dir = ref None in
  let dir = ref None in
  let inc = ref None in
  let str = ref None in
  Arg.parse
    [
      "-b",
      Arg.String (fun s -> base_dir := Some s),
      "<dir>  Base directory";
      "-d",
      Arg.String (fun s -> dir := Some s),
      "<dir>  Parse problems in directory <dir> and its subdirectories";
      "-i",
      Arg.String (fun s -> inc := Some s),
      "<dir>  Parse problems in directory <dir> and its subdirectories;\n" ^
      "            included files are parsed too";
      "-s",
      Arg.String (fun s -> str := Some s),
      "<str>  Parse string <str> and then pretty-print it";
    ]
    (fun _ -> failwith "Invalid argument")
    "Test runner for TPTP library";

  match !dir with
    | Some d ->
        Printf.printf "Parsing problems in %s\n" d;
        parse_tptp_problems d
    | None ->
  match !inc with
    | Some d ->
        Printf.printf "Parsing problems in %s with included files\n" d;
        parse_tptp_problems_inc !base_dir d
    | None ->
  match !str with
    | Some s ->
        Printf.printf "Parsing string:\n%s\n\n" s;
        parse_tptp_string s
    | None ->
        Printf.printf "Running unit tests\n";
        ignore (run_test_tt suite)
