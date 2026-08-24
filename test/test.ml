open OUnit2
open Enigma

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

(* [is_involution w] holds when [map_refl w] undoes itself at every
   position, i.e. w(w(i)) = i for all i in 0..25. That property is what
   makes a wiring specification a valid *reflector* specification. *)
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

let suite =
  "enigma test suite"
  >::: List.flatten
         [
           index_tests;
           map_r_to_l_tests;
           map_l_to_r_tests;
           map_refl_tests;
(*         map_plug_tests; *)
(*         cipher_char_tests; *)
(*         step_tests; *)
(*         cipher_tests; *)
         ]

let () = run_test_tt_main suite
