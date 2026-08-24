open OUnit2
open Enigma

(* ---- the historical Enigma I components ---- *)

let rotor_i = "EKMFLGDQVZNTOWYHXUSPAIBRCJ"
let rotor_ii = "AJDKSIRUXBLHWTMCQGZNPYFVOE"
let rotor_iii = "BDFHJLCPRTXVZNYEIWGAKMUSQO"

let refl_id = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
let refl_b = "YRUHQSLDPXNGOKMIEBFZCWVJAT"
let refl_c = "FVPJIAOYEDRZXWGCTKUQSBNMHL"

(*
  [letter i] is the [i]th letter of the alphabet. Enigma has its own private
  [letter], but it is not exported by enigma.mli, so the tests keep a copy.
*)
let letter i = Char.chr (i + Char.code 'A')
let alphabet = List.init 26 letter
let positions = List.init 26 Fun.id

(* ---- machines under test ---- *)

(*
  [oriented w top] is rotor [w] installed with [top] showing. The turnover
  only matters from Step 9 on, so it defaults to an arbitrary letter.
*)
let oriented ?(turnover = 'Z') w top =
  { rotor = { wiring = w; turnover }; top_letter = top }

(*
  Reflector B, rotors I-II-III left to right, all showing 'A', no cables:
  the machine of the handout's Step 8 worked example.
*)
let handout_config = {
  refl = refl_b;
  rotors = [
    oriented rotor_i 'A';
    oriented rotor_ii 'A';
    oriented rotor_iii 'A'
  ];
  plugboard = []
}

let staggered_config = {
  handout_config with
  rotors = [
    oriented rotor_i 'Q';
    oriented rotor_ii 'E';
    oriented rotor_iii 'V'
  ]
}

let plugged_config =
  { handout_config with plugboard = [('A', 'M'); ('Q', 'X')] }

let duplicate_rotors_config =
  { handout_config with rotors = [oriented rotor_i 'A'; oriented rotor_i 'A'] }

let no_rotors_config = { handout_config with rotors = [] }
let identity_machine = { refl = refl_id; rotors = []; plugboard = [] }
let one_cable_machine = { identity_machine with plugboard = [('A', 'Z')] }

(* Rotor I alone, showing [top]. *)
let rotor_i_only top =
  { handout_config with rotors = [oriented ~turnover:'Q' rotor_i top] }

(* Rotors II-I left to right, showing the two top letters of [state]. *)
let ii_i state = {
  handout_config with
  rotors = [
    oriented ~turnover:'E' rotor_ii state.[0];
    oriented ~turnover:'Q' rotor_i  state.[1]
  ]
}

(* Rotors III-II-I left to right with their historical turnovers (V, E, Q),
   showing the three top letters of [state]. *)
let iii_ii_i state = {
  handout_config with
  rotors = [
    oriented ~turnover:'V' rotor_iii state.[0];
    oriented ~turnover:'E' rotor_ii  state.[1];
    oriented ~turnover:'Q' rotor_i   state.[2]
  ]
}

(* The handout's Step 10 machine: rotors I-II-III showing F-U-N, one cable. *)
let ocaml_config = {
  refl = refl_b;
  rotors = [
    oriented ~turnover:'Q' rotor_i   'F';
    oriented ~turnover:'E' rotor_ii  'U';
    oriented ~turnover:'V' rotor_iii 'N'
  ];
  plugboard = [('A', 'Z')]
}

(* ---- small utilities ---- *)

(* [get_state cfg] is the top letters of [cfg]'s rotors, left to right. *)
let get_state config = config.rotors
  |> List.map (fun r -> r.top_letter)
  |> List.to_seq
  |> String.of_seq

let show_char c = Printf.sprintf "%C" c
let show_string s = Printf.sprintf "%S" s
let show_states l = l |> List.map show_string |> String.concat "; "

let distinct_chars s = s
  |> String.to_seq
  |> List.of_seq
  |> List.sort_uniq compare

(*
  ---- case builders ----

  Each builder wraps the call under test inside [fun _ -> ...], so it runs
  when the suite runs rather than when these lists are built. A raised
  exception then fails one case instead of aborting the whole suite.
*)

let index_case c expected =
  Printf.sprintf "index %C" c >:: fun _ ->
    assert_equal ~printer:string_of_int expected (c |> index)

(* Shared by map_r_to_l and map_l_to_r: same shape, same argument order. *)
let rotor_case name f expected wiring top pos =
  name >:: fun _ ->
    assert_equal ~printer:string_of_int expected (f wiring top pos)

let refl_case name expected wiring pos =
  name >:: fun _ ->
    assert_equal ~printer:string_of_int expected (pos |> map_refl wiring)

let plug_case name expected board c =
  name >:: fun _ ->
    assert_equal ~printer:show_char expected (c |> map_plug board)

let char_case name expected config c =
  name >:: fun _ ->
    assert_equal ~printer:show_char expected (c |> cipher_char config)

let cipher_case name expected config s =
  name >:: fun _ ->
    assert_equal ~printer:show_string expected (s |> cipher config)

(* [step_case name expected cfg] checks the top letters after one step. *)
let step_case name expected config =
  name >:: fun _ ->
    assert_equal ~printer:show_string expected (config |> step |> get_state)

(* [holds name prop cfg] checks that a property holds of a whole machine. *)
let holds name prop config =
  name >:: fun _ -> assert_bool name (config |> prop)

(* ---- Step 3: index ---- *)

let index_tests = [
  index_case 'A' 0;
  index_case 'B' 1;
  index_case 'C' 2;
  index_case 'Z' 25;
  index_case 'O' 14;
]

(* ---- Step 5: rotors ---- *)

let map_r_to_l_tests = [
  rotor_case "r_to_l identity wiring top A" map_r_to_l  0 refl_id   'A'  0;
  rotor_case "r_to_l rotorI top A"          map_r_to_l  4 rotor_i   'A'  0;
  rotor_case "r_to_l rotorI top B"          map_r_to_l  9 rotor_i   'B'  0;
  rotor_case "r_to_l rotorIII wraps both"   map_r_to_l 17 rotor_iii 'O' 14;
]

let map_l_to_r_tests = [
  rotor_case "l_to_r identity wiring top A" map_l_to_r  0 refl_id 'A'  0;
  rotor_case "l_to_r rotorI top A"          map_l_to_r 20 rotor_i 'A'  0;
  rotor_case "l_to_r rotorI top B"          map_l_to_r 21 rotor_i 'B'  0;
  rotor_case "l_to_r rotorI top F pos 10"   map_l_to_r 14 rotor_i 'F' 10;
]

(* ---- Step 6: reflector ---- *)

(*
  [is_involution w] holds when [map_refl w] undoes itself at every position,
  i.e. w(w(i)) = i for all i. That property is what makes a wiring
  specification a valid *reflector* specification.
*)
let is_involution w =
  positions |> List.for_all (fun i -> map_refl w (map_refl w i) = i)

let map_refl_tests = [
  refl_case "refl identity pos 0"   0 refl_id  0;
  refl_case "refl identity pos 25" 25 refl_id 25;
  refl_case "refl B pos 5"         18 refl_b   5;
  refl_case "refl B pos 0"         24 refl_b   0;
  refl_case "refl B pos 24"         0 refl_b  24;
  refl_case "refl C pos 12"        23 refl_c  12;

  "refl B is an involution" >:: (fun _ ->
    assert_bool "reflector B" (is_involution refl_b));
  "refl C is an involution" >:: (fun _ ->
    assert_bool "reflector C" (is_involution refl_c));
]

(* ---- Step 7: plugboard ---- *)

let two_cables = [('A', 'Z'); ('X', 'Y')]

(* A maximal plugboard: 13 cables, every letter plugged. *)
let full_board = [
  ('A','Z'); ('B','Y'); ('C','X'); ('D','W'); ('E','V'); ('F','U'); ('G','T');
  ('H','S'); ('I','R'); ('J','Q'); ('K','P'); ('L','O'); ('M','N')
]

(*
  The plugboard is self-inverse: unplugging a letter and plugging it back
  returns the original. Holds for every letter, on any valid board.
*)
let plug_self_inverse board =
  alphabet |> List.for_all (fun c -> map_plug board (map_plug board c) = c)

let map_plug_tests = [
  plug_case "plug empty board"          'A' []          'A';
  plug_case "plug 1 cable, left side"   'Z' [('A','Z')] 'A';
  plug_case "plug 1 cable, right side"  'A' [('A','Z')] 'Z';
  plug_case "plug 2 cables, tail cable" 'Y' two_cables  'X';
  plug_case "plug 2 cables, head cable" 'X' [('X','Y'); ('A','Z')] 'Y';

  (* Non-empty board, unplugged letter: must pass through unchanged. *)
  plug_case "plug unplugged letter"     'M' two_cables  'M';
  (* The 13th cable, so the recursion has to walk the whole list. *)
  plug_case "plug deep in list, left"   'N' full_board  'M';
  plug_case "plug deep in list, right"  'M' full_board  'N';
  plug_case "plug full board, first"    'Z' full_board  'A';

  "plug full board is total" >:: (fun _ ->
    assert_bool "full board" (plug_self_inverse full_board));
  "plug partial board is total" >:: (fun _ ->
    assert_bool "partial board" (plug_self_inverse two_cables));
]

(* ---- Step 8: ciphering a character ----

   Three properties, each checked across all 26 input letters. *)

(*
  Enigma is self-inverse: enciphering the ciphertext under the same
  configuration recovers the plaintext. This is why the receiving operator
  could decrypt by simply retyping what they received.
*)
let self_inverse config =
  alphabet |> List.for_all (fun c -> cipher_char config (cipher_char config c) = c)

(*
  No letter ever enciphers to itself. Follows from the reflector being
  fixed-point-free, and was a decisive weakness at Bletchley Park: it let
  cryptanalysts discard candidate crib alignments on sight.
*)
let no_fixed_point config =
  alphabet |> List.for_all (fun c -> cipher_char config c <> c)

(* The cipher is a permutation of the alphabet: 26 distinct outputs. *)
let is_permutation config = alphabet
  |> List.map (cipher_char config)
  |> List.sort_uniq compare
  |> List.length
  |> ( = ) 26

let cipher_char_tests = [
  (* No plugs, no rotors, identity reflector: the identity function. *)
  char_case "identity machine" 'A' identity_machine 'A';

  (* The handout's Step 8 worked example: 'G' enciphers to 'P'. *)
  char_case "handout worked example" 'P' handout_config 'G';

  (*
    A plugboard must be crossed on the way out as well as the way in. With
    A<->Z cabled and nothing else in the machine, 'A' plugs to 'Z', passes
    through unchanged, then plugs back to 'A'.
  *)
  char_case "plugboard applied on both sides" 'A' one_cable_machine 'A';

  (*
    The handout's full Step 8 table, all 26 letters at once:
      input:  ABCDEFGHIJKLMNOPQRSTUVWXYZ
      output: UEJOBTPZWCNSRKDGVMLFAQIYXH
  *)
  "handout full alphabet table" >:: (fun _ ->
    let expected = "UEJOBTPZWCNSRKDGVMLFAQIYXH" in
    assert_bool "every letter matches the handout table"
      (positions
       |> List.for_all (fun i -> cipher_char handout_config (letter i) = expected.[i])));

  holds "self-inverse: handout config"       self_inverse handout_config;
  holds "self-inverse: with plugboard"       self_inverse plugged_config;
  holds "self-inverse: staggered top letters" self_inverse staggered_config;
  holds "self-inverse: no rotors"            self_inverse no_rotors_config;
  holds "self-inverse: duplicate rotors"     self_inverse duplicate_rotors_config;

  holds "no letter ciphers to itself"        no_fixed_point handout_config;
  holds "no fixed point: with plugboard"     no_fixed_point plugged_config;

  holds "cipher is a permutation"            is_permutation handout_config;
  holds "permutation: staggered top letters" is_permutation staggered_config;
]

(* ---- Step 9: stepping ---- *)

(* [trace state n] is the [n] top-letter states visited from [state]. *)
let trace state n =
  let rec loop config i acc =
    if i = 0 then List.rev acc
    else loop (config |> step) (i - 1) (get_state config :: acc)
  in
  loop (iii_ii_i state) n []

let rec step_times n config = if n = 0 then config else step_times (n - 1) (step config)

let step_tests = [
  (* -- Rule 1: the rightmost rotor always steps -- *)
  step_case "rule 1: lone rotor steps"         "B" (rotor_i_only 'A');
  step_case "rule 1: top letter wraps Z to A"  "A" (rotor_i_only 'Z');
  step_case "rule 1: no rotors, nothing to step" "" no_rotors_config;

  (* -- Rule 2: at its turnover, a rotor takes its left neighbour with it -- *)
  step_case "rule 2: turnover drags left neighbour" "BR" (ii_i "AQ");

  (*
    Rule 2 explicitly does not apply to the leftmost rotor: it has no left
    neighbour, so its own turnover never makes it step.
  *)
  step_case "rule 2: leftmost at own turnover no step" "EB" (ii_i "EA");

  (*
    -- Rule 3: no rotor steps twice for one letter --
    Rotor I is at its turnover, so it drags rotor II. Rotor II is also at its
    own turnover, so it drags rotor III. Rule 3 caps rotor II at one step.
  *)
  step_case "rule 3: middle rotor steps at most once" "BFR" (iii_ii_i "AEQ");

  (* -- the handout's two worked sequences -- *)
  ("handout example 1: KDO..." >:: fun _ ->
    assert_equal ~printer:show_states
      ["KDO"; "KDP"; "KDQ"; "KER"; "LFS"; "LFT"; "LFU"] (trace "KDO" 7));

  (* This one is why the handout insists there are no typos: rotor III starts
     on its own turnover 'V' and must not move until pushed. *)
  ("handout example 2: VDP..." >:: fun _ ->
    assert_equal ~printer:show_states
      ["VDP"; "VDQ"; "VER"; "WFS"; "WFT"] (trace "VDP" 5));

  (* -- structural properties -- *)

  (* [step] returns a new config; the original must be untouched. That is the
     point of the config -> config type. *)
  ("step does not mutate its argument" >:: fun _ ->
    let before = iii_ii_i "KDO" in
    let _ = before |> step in
    assert_equal ~printer:show_string "KDO" (before |> get_state));

  ("step changes only the rotors" >:: fun _ ->
    let before = { (iii_ii_i "KDO") with plugboard = [('A','M')] } in
    let after = before |> step in
    assert_equal before.refl after.refl;
    assert_equal before.plugboard after.plugboard;
    assert_equal (List.length before.rotors) (List.length after.rotors));

  ("step preserves wiring and turnovers" >:: fun _ ->
    let before = iii_ii_i "KDO" in
    let after = before |> step in
    assert_equal
      (before.rotors |> List.map (fun r -> r.rotor))
      (after.rotors  |> List.map (fun r -> r.rotor)));

  (* A lone rotor has period 26: 26 steps return it to where it started. *)
  ("lone rotor has period 26" >:: fun _ ->
    assert_equal ~printer:show_string "A"
      (rotor_i_only 'A' |> step_times 26 |> get_state));
]

(* ---- Step 10: ciphering a string ---- *)

(*
  A message long enough to drive the rightmost rotor past its turnover several
  times, so the tests below exercise stepping, not just wiring.
*)
let long_message = String.init 60 (fun i -> letter (i * 7 mod 26))

(* [round_trip name cfg s] checks that enciphering [s] twice returns [s]. *)
let round_trip name config s =
  name >:: fun _ ->
    assert_equal ~printer:show_string s (s |> cipher config |> cipher config)

let cipher_tests = [
  (* -- the handout's worked case -- *)
  cipher_case "handout: YNGXQ deciphers to a language"
    "OCAML" ocaml_config "YNGXQ";

  (* Same machine, run backwards: the receiving operator sets the same key
     and retypes the ciphertext. *)
  cipher_case "handout: OCAML enciphers back to YNGXQ"
    "YNGXQ" ocaml_config "OCAML";

  (* -- degenerate and ordering cases -- *)
  cipher_case "empty string ciphers to empty string"
    "" ocaml_config "";

  (*
    The machine steps BEFORE enciphering, so a one-character message must
    agree with cipher_char applied to the already-stepped config. Encipher
    before stepping and this is the test that catches it.
  *)
  cipher_case "steps before enciphering the first letter"
    ('Y' |> cipher_char (step ocaml_config) |> String.make 1) ocaml_config "Y";

  ("output has the same length as input" >:: fun _ ->
    assert_equal ~printer:string_of_int
      (long_message |> String.length)
      (long_message |> cipher ocaml_config |> String.length));

  (* -- properties over a long message --

     Self-inverse, now end to end: step, cipher_char and every function
     underneath, across 60 letters and several turnovers. *)
  round_trip "self-inverse over a long message"   ocaml_config long_message;
  round_trip "self-inverse with an empty plugboard"
    { ocaml_config with plugboard = [] } long_message;
  round_trip "self-inverse with no rotors"
    { ocaml_config with rotors = [] } long_message;

  (* No letter ever enciphers to itself, position by position. *)
  ("no letter ciphers to itself" >:: fun _ ->
    let out = long_message |> cipher ocaml_config in
    assert_bool "some position was unchanged"
      (List.init (String.length long_message) Fun.id
       |> List.for_all (fun i -> long_message.[i] <> out.[i])));

  (*
    Enigma is polyalphabetic: the rotors move, so a run of one letter must
    NOT encipher to a run of one letter. This is what separates cipher from
    "map cipher_char over the string".
  *)
  ("repeated letter gives a varied output" >:: fun _ ->
    assert_bool "output was monoalphabetic"
      (String.make 30 'A'
       |> cipher ocaml_config
       |> distinct_chars
       |> List.length
       |> ( < ) 1));

  (*
    [cipher] is a function, not a machine with hidden state: running it twice
    on the same config must give the same answer.
  *)
  ("cipher is pure" >:: fun _ ->
    assert_equal ~printer:show_string
      (long_message |> cipher ocaml_config)
      (long_message |> cipher ocaml_config));

  (* Ciphering leaves the caller's config untouched. *)
  ("cipher does not disturb its config" >:: fun _ ->
    let before = ocaml_config |> get_state in
    let _ = long_message |> cipher ocaml_config in
    assert_equal ~printer:show_string before (ocaml_config |> get_state));

  (*
    Starting the rightmost rotor one letter earlier gives a different
    ciphertext: the key setting actually matters.
  *)
  ("a different key gives a different ciphertext" >:: fun _ ->
    let other = {
      ocaml_config with
      rotors = [
        oriented ~turnover:'Q' rotor_i   'F';
        oriented ~turnover:'E' rotor_ii  'U';
        oriented ~turnover:'V' rotor_iii 'M'
      ]
    } in
    assert_bool "key setting had no effect"
      (cipher ocaml_config long_message <> cipher other long_message));
]

let suite = "enigma test suite" >::: List.flatten [
    index_tests;
    map_r_to_l_tests;
    map_l_to_r_tests;
    map_refl_tests;
    map_plug_tests;
    cipher_char_tests;
    step_tests;
    cipher_tests;
  ]

let () = run_test_tt_main suite
