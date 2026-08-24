open OUnit2
open Enigma

(* ---- shared fixtures: the historical Enigma I components ---- *)
let rotor_i = "EKMFLGDQVZNTOWYHXUSPAIBRCJ"
let rotor_ii = "AJDKSIRUXBLHWTMCQGZNPYFVOE"
let rotor_iii = "BDFHJLCPRTXVZNYEIWGAKMUSQO"

let refl_id = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
let refl_b = "YRUHQSLDPXNGOKMIEBFZCWVJAT"

(*
  [letter i] is the [i]th letter of the alphabet. Enigma has its own private
  [letter], but it is not exported by enigma.mli, so the tests keep a copy.
*)
let letter i = Char.chr (i + Char.code 'A')
let alphabet = List.init 26 letter

let index_tests = [
  ("index A" >:: fun _ -> assert_equal  0 (index 'A'));
  ("index B" >:: fun _ -> assert_equal  1 (index 'B'));
  ("index C" >:: fun _ -> assert_equal  2 (index 'C'));
  ("index Z" >:: fun _ -> assert_equal 25 (index 'Z'));
  ("index O" >:: fun _ -> assert_equal 14 (index 'O'));
]

let map_r_to_l_tests = [
  ("r_to_l identity wiring top A" >:: fun _ ->
    assert_equal  0 (map_r_to_l "ABCDEFGHIJKLMNOPQRSTUVWXYZ" 'A'  0));
  ("r_to_l rotorI top A"          >:: fun _ ->
    assert_equal  4 (map_r_to_l "EKMFLGDQVZNTOWYHXUSPAIBRCJ" 'A'  0));
  ("r_to_l rotorI top B"          >:: fun _ ->
    assert_equal  9 (map_r_to_l "EKMFLGDQVZNTOWYHXUSPAIBRCJ" 'B'  0));
  ("r_to_l rotorIII wraps both"   >:: fun _ ->
    assert_equal 17 (map_r_to_l "BDFHJLCPRTXVZNYEIWGAKMUSQO" 'O' 14));
]

let map_l_to_r_tests = [
  ("l_to_r identity wiring top A"     >:: fun _ ->
    assert_equal  0 (map_l_to_r "ABCDEFGHIJKLMNOPQRSTUVWXYZ" 'A'  0));
  ("l_to_r rotorI top A"              >:: fun _ ->
    assert_equal 20 (map_l_to_r "EKMFLGDQVZNTOWYHXUSPAIBRCJ" 'A'  0));
  ("l_to_r rotorI top B"              >:: fun _ ->
    assert_equal 21 (map_l_to_r "EKMFLGDQVZNTOWYHXUSPAIBRCJ" 'B'  0));
  ("l_to_r rotorI top F input_pos 10" >:: fun _ ->
    assert_equal 14 (map_l_to_r "EKMFLGDQVZNTOWYHXUSPAIBRCJ" 'F' 10));
]

(*
  [is_involution w] holds when [map_refl w] undoes itself at every
  position, i.e. w(w(i)) = i for all i in 0..25. That property is what
  makes a wiring specification a valid *reflector* specification.
*)
let is_involution w =
  List.for_all (fun i -> map_refl w (map_refl w i) = i) (List.init 26 Fun.id)

let map_refl_tests = [
  ("refl identity pos 0"     >:: fun _ ->
    assert_equal  0 (map_refl "ABCDEFGHIJKLMNOPQRSTUVWXYZ"  0));
  ("refl identity pos 25"    >:: fun _ ->
    assert_equal 25 (map_refl "ABCDEFGHIJKLMNOPQRSTUVWXYZ" 25));
  ("refl B pos 5"            >:: fun _ ->
    assert_equal 18 (map_refl "YRUHQSLDPXNGOKMIEBFZCWVJAT"  5));
  ("refl B pos 0"            >:: fun _ ->
    assert_equal 24 (map_refl "YRUHQSLDPXNGOKMIEBFZCWVJAT"  0));
  ("refl B pos 24"           >:: fun _ ->
    assert_equal  0 (map_refl "YRUHQSLDPXNGOKMIEBFZCWVJAT" 24));
  ("refl C pos 12"           >:: fun _ ->
    assert_equal 23 (map_refl "FVPJIAOYEDRZXWGCTKUQSBNMHL" 12));

  ("refl B is an involution" >:: fun _ ->
    assert_bool "reflector B" (is_involution "YRUHQSLDPXNGOKMIEBFZCWVJAT"));
  ("refl C is an involution" >:: fun _ ->
    assert_bool "reflector C" (is_involution "FVPJIAOYEDRZXWGCTKUQSBNMHL"));
]

let full_board =
  [ ('A','Z'); ('B','Y'); ('C','X'); ('D','W'); ('E','V'); ('F','U'); ('G','T');
    ('H','S'); ('I','R'); ('J','Q'); ('K','P'); ('L','O'); ('M','N') ]

(*
  The plugboard is self-inverse: unplugging a letter and plugging it back
  returns the original. Holds for every letter, on any valid board.
*)
let plug_self_inverse board =
  List.for_all
    (fun i -> let c = Char.chr (i + Char.code 'A') in
              map_plug board (map_plug board c) = c)
    (List.init 26 Fun.id)

let map_plug_tests = [
  ("plug empty board"            >:: fun _ ->
    assert_equal 'A' (map_plug [] 'A'));
  ("plug 1 cable, left side"     >:: fun _ ->
    assert_equal 'Z' (map_plug [('A','Z')] 'A'));
  ("plug 1 cable, right side"    >:: fun _ ->
    assert_equal 'A' (map_plug [('A','Z')] 'Z'));
  ("plug 2 cables, tail cable"   >:: fun _ ->
    assert_equal 'Y' (map_plug [('A','Z');('X','Y')] 'X'));
  ("plug 2 cables, head cable"   >:: fun _ ->
    assert_equal 'X' (map_plug [('X','Y');('A','Z')] 'Y'));

  ("plug unplugged letter"       >:: fun _ ->
    assert_equal 'M' (map_plug [('A','Z');('X','Y')] 'M'));
  ("plug deep in list, left"     >:: fun _ ->
    assert_equal 'N' (map_plug full_board 'M'));
  ("plug deep in list, right"    >:: fun _ ->
    assert_equal 'M' (map_plug full_board 'N'));
  ("plug full board, first"      >:: fun _ ->
    assert_equal 'Z' (map_plug full_board 'A'));

  ("plug full board is total"    >:: fun _ ->
    assert_bool "full board" (plug_self_inverse full_board));
  ("plug partial board is total" >:: fun _ ->
    assert_bool "partial board" (plug_self_inverse [('A','Z');('X','Y')]));
]


(* ---- 3 properties, each checked across all 26 input letters ---- *)

(*
  Enigma is self-inverse: enciphering the ciphertext under the same
  configuration recovers the plaintext.

  This is why the receiving operator
  could decrypt by simply retyping what they received.
*)
let self_inverse cfg =
  List.for_all (fun c -> cipher_char cfg (cipher_char cfg c) = c) alphabet

(*
  No letter ever enciphers to itself.
  Follows from the reflector being fixed-point-free.
*)
let no_fixed_point cfg =
  List.for_all (fun c -> cipher_char cfg c <> c) alphabet

(* The cipher is a permutation of the alphabet: 26 distinct outputs. *)
let is_permutation cfg =
  List.length (
    List.sort_uniq
      compare
      (List.map (cipher_char cfg) alphabet)
  ) = 26

(*
  [oriented w top] is rotor [w] installed with [top] showing.
  [turnover] is unused until Step 9, so it is arbitrary here.
*)
let oriented w top = {
  rotor = {
    wiring = w;
    turnover = 'Z'
  };
  top_letter = top
}


let handout_config = {
  refl = refl_b;
  rotors = [
    oriented rotor_i 'A';
    oriented rotor_ii 'A';
    oriented rotor_iii 'A'
  ];
  plugboard = []
}

let cipher_char_tests = [
    (* Identity machine: no plugs, no rotors, identity reflector. *)
    ( "identity machine" >:: fun _ ->
      assert_equal 'A'
        (cipher_char
           { (* config *)
             refl = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
             rotors = [];
             plugboard = [];
           }
           'A'
        )
    );

    ( "example"          >:: fun _ ->
      assert_equal 'P'
        (cipher_char
           {
             refl = "YRUHQSLDPXNGOKMIEBFZCWVJAT";
             rotors = [
               {
                 rotor = {
                   wiring = "EKMFLGDQVZNTOWYHXUSPAIBRCJ";
                   turnover = 'Z'
                 };
                 top_letter = 'A'
               };
               {
                 rotor = {
                   wiring = "AJDKSIRUXBLHWTMCQGZNPYFVOE";
                   turnover = 'Z'
                };
                 top_letter = 'A'
               };
               {
                 rotor = {
                   wiring = "BDFHJLCPRTXVZNYEIWGAKMUSQO";
                   turnover = 'Z'
                };
                 top_letter = 'A'
               };
             ];
             plugboard = [];
           }
           'G'
        )
    );

    (* The handout's full Step 8 table, all 26 letters at once:
         input:  ABCDEFGHIJKLMNOPQRSTUVWXYZ
         output: UEJOBTPZWCNSRKDGVMLFAQIYXH *)
    ( "handout full alphabet table" >:: fun _ ->
      let expected = "UEJOBTPZWCNSRKDGVMLFAQIYXH" in
      assert_bool "every letter matches the handout table"
        (List.for_all
           (fun i -> cipher_char handout_config (letter i) = expected.[i])
           (List.init 26 Fun.id)
        )
    );

    (* A plugboard must be crossed on the way out as well as the way in.
       With A<->Z cabled and nothing else in the machine, 'A' plugs to 'Z',
       passes through unchanged, then plugs back to 'A'. *)
    ( "plugboard applied on both sides" >:: fun _ ->
      assert_equal 'A'
        (cipher_char
           {
             refl = refl_id;
             rotors = [];
             plugboard = [('A', 'Z')]
           }
           'A'
        )
    );

    (* --- properties over all 26 letters --- *)

    ( "self-inverse: handout config" >:: fun _ ->
      assert_bool "handout"
        (self_inverse handout_config)
    );

    ( "self-inverse: with plugboard" >:: fun _ ->
      assert_bool "plugged"
        (self_inverse {handout_config with plugboard = [('A', 'M');('Q', 'X')]})
    );

    ( "self-inverse: staggered top letters" >:: fun _ ->
      assert_bool "staggered"
        (self_inverse
           {
             handout_config with
             rotors = [
               oriented rotor_i 'Q';
               oriented rotor_ii 'E';
               oriented rotor_iii 'V'
             ]
           }
        )
    );

    ( "self-inverse: no rotors" >:: fun _ ->
      assert_bool "bare"
        (self_inverse {refl = refl_b; rotors = []; plugboard = []})
    );

    ( "self-inverse: duplicate rotors" >:: fun _ ->
      assert_bool "dupes"
        (self_inverse
           {
             handout_config with
             rotors = [
               oriented rotor_i 'A';
               oriented rotor_i 'A'
             ]
           }
        )
    );

    ( "no letter ciphers to itself" >:: fun _ ->
      assert_bool "handout"
        (no_fixed_point handout_config)
    );

    ( "no fixed point: with plugboard" >:: fun _ ->
      assert_bool "plugged"
        (no_fixed_point
           {handout_config with plugboard = [('A', 'M');('Q', 'X')]}
        )
    );

    ( "cipher is a permutation" >:: fun _ ->
      assert_bool "handout"
        (is_permutation handout_config)
    );

    ( "permutation: staggered top letters" >:: fun _ ->
      assert_bool "staggered"
        (is_permutation
           { handout_config with
             rotors = [
               oriented rotor_i 'Q';
               oriented rotor_ii 'E';
               oriented rotor_iii 'V'
             ]
           }
        )
    );
  ]
(*

let step_tests = []

let cipher_tests = []
*)


let suite =
  "enigma test suite"
  >::: List.flatten
         [
           index_tests;
           map_r_to_l_tests;
           map_l_to_r_tests;
           map_refl_tests;
           map_plug_tests;
           cipher_char_tests;
(*         step_tests; *)
(*         cipher_tests; *)
         ]

let () = run_test_tt_main suite
