(* Copyright (c) 2012 Radek Micek *)

open OUnit
open Tptp_ast

let with_dispose dispose f x =
  let result =
    try
      f x
    with
      | e -> dispose x; raise e in

  dispose x;
  result

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
  assert_equal ast real_ast;
  match real_exn with
    | None -> ()
    | Some e -> raise e

let assert_parses_and_raises ast str =
  let real_ast, real_exn = parse_string str in
  assert_equal ast real_ast;
  match real_exn with
    | None -> assert_failure "No exception raised"
    | Some (Tptp.Parse_error (_, _)) -> ()
    | Some e -> raise e

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
  ] in

  assert_parses ast str

let test_reject_keyword_as_pred () =
  let str = "fof(0, axiom, cnf(X))." in
  assert_parses_and_raises [] str

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
  let str = "% hello \255\032\254\020" in
  let ast = [ Comment (to_comment_line " hello \255\032\254") ] in
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

(* TODO: Update lexer or remove this test. *)
let test_reject_comment_block_inv_char () =
  skip_if true "";
  let str = "/* \000 */" in
  assert_parses_and_raises [] str

(* TODO *)
let test_parse_annotations () =
  skip_if true ""

(* TODO: Test following functions for failure:

     to_var
     to_plain_word
     to_defined_word
     to_system_word
     to_tptp_string
     to_comment_line
*)

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
      "reject keyword as predicate" >:: test_reject_keyword_as_pred;
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
      "reject comment block with invalid character" >::
        test_reject_comment_block_inv_char;
      "parse annotations" >:: test_parse_annotations;
    ]

(* TODO: Add option to test parser by parsing all FOF and CNF problems in TPTP. *)
let _ =
  run_test_tt_main suite
