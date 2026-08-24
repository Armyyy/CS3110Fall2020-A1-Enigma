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
let oriented ?(turnover = 'Z') w top = {
  rotor = {
    wiring = w;
    turnover = turnover
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

let get_state config = config.rotors
  |> List.map (fun a -> a.top_letter)
  |> List.to_seq
  |> String.of_seq

(*
  [iii_ii_i state] is the machine with rotors III-II-I installed left to
  right, carrying their historical turnovers (V, E, Q), showing the three
  top letters of [state].
*)
let iii_ii_i state =
  { handout_config with
    rotors = [
      oriented ~turnover:'V' rotor_iii state.[0];
      oriented ~turnover:'E' rotor_ii  state.[1];
      oriented ~turnover:'Q' rotor_i   state.[2]
    ]
  }

let trace state n = let rec loop cfg i acc =
    if i = 0 then List.rev acc
    else loop (step cfg) (i - 1) (get_state cfg::acc)
  in loop (iii_ii_i state) n []

let step_tests = [
  (* ---- Rule 1: the rightmost rotor always steps ---- *)

  ("rule 1: lone rotor steps" >:: fun _ -> assert_equal "B"
    (get_state (step
      {handout_config with rotors = [oriented ~turnover:'Q' rotor_i 'A']}
    ))
  );

  ("rule 1: top letter wraps Z to A" >:: fun _ -> assert_equal "A"
    (get_state (step
      {handout_config with rotors = [oriented ~turnover:'Q' rotor_i 'Z']}
    ))
  );

  ("rule 1: no rotors, nothing to step" >:: fun _ -> assert_equal ""
    (get_state (step
      {handout_config with rotors = []}
    ))
  );

  (* ---- Rule 2: when at its turnover, also takes its left neighbour ---- *)

  ("rule 2: turnover drags left neighbour" >:: fun _ -> assert_equal "BR"
    (get_state (step
      {
        handout_config with
        rotors = [
          oriented ~turnover:'E' rotor_ii 'A';
          oriented ~turnover:'Q' rotor_i  'Q'
        ]
      }
    ))
  );

  (*
    Rule 2 explicitly does not apply to the leftmost rotor: it has no left
    neighbour, so its own turnover never makes it step.
  *)
  ("rule 2: leftmost at own turnover no step" >:: fun _ -> assert_equal "EB"
    (get_state (step
      {
        handout_config with
        rotors = [
          oriented ~turnover:'E' rotor_ii 'E';  (* at its turnover, leftmost *)
          oriented ~turnover:'Q' rotor_i  'A'
        ]
      }
    ))
  );

  (* ---- Rule 3: no rotor steps twice ---- *)

  (*
    Rotor I is at its turnover, so it drags rotor II. Rotor II is also at
    its own turnover, so it drags rotor III. Rule 3 caps rotor II at one step.
  *)
  ("rule 3: middle rotor steps at most once" >:: fun _ -> assert_equal "BFR"
    (get_state (step (iii_ii_i "AEQ")))
  );

  (* ---- the handout's two worked sequences ---- *)

  ("handout example 1: KDO..." >:: fun _ ->
    assert_equal ["KDO"; "KDP"; "KDQ"; "KER"; "LFS"; "LFT"; "LFU"]
      (trace "KDO" 7)
  );

  ("handout example 2: VDP..." >:: fun _ ->
    assert_equal ["VDP"; "VDQ"; "VER"; "WFS"; "WFT"]
      (trace "VDP" 5)
  );

  (* ---- structural properties ---- *)

  (* [step] returns a new config; the original must be untouched. *)
  ("step does not mutate its argument" >:: fun _ ->
    let before = iii_ii_i "KDO" in
    let _ = step before in
    assert_equal "KDO" (get_state before)
  );

  ("step changes only the rotors" >:: fun _ ->
    let before = { (iii_ii_i "KDO") with plugboard = [('A','M')] } in
    let after = step before in
    assert_equal before.refl after.refl;
    assert_equal before.plugboard after.plugboard;
    assert_equal (List.length before.rotors) (List.length after.rotors)
  );

  ("step preserves wiring and turnovers" >:: fun _ ->
    let before = iii_ii_i "KDO" in
    let after = step before in
    assert_equal
      (List.map (fun r -> r.rotor) before.rotors)
      (List.map (fun r -> r.rotor) after.rotors)
  );

  (* A lone rotor has period 26: 26 steps return it to where it started. *)
  ("lone rotor has period 26" >:: fun _ ->
    let start = {
      handout_config with rotors = [oriented ~turnover:'Q' rotor_i 'A']
    } in
    let rec times n cfg = if n = 0 then cfg else times (n - 1) (step cfg) in
    assert_equal "A" (get_state (times 26 start)));
]

(*
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
           step_tests;
(*         cipher_tests; *)
         ]

let () = run_test_tt_main suite
