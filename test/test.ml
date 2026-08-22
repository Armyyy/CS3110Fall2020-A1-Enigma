open OUnit2
open Enigma

let index_tests = [
  ("index A" >:: fun _ ->
    assert_equal 0 (index 'A'));
  ("index B" >:: fun _ ->
    assert_equal 1 (index 'B'));
  ("index C" >:: fun _ ->
    assert_equal 2 (index 'C'));
  ("index Z" >:: fun _ ->
    assert_equal 25 (index 'Z'));
]

let map_r_to_l_tests = [
    (* Example 1 from the handout: wiring EKMFLGDQVZNTOWYHXUSPAIBRCJ,
       top letter 'A', input position 0, output position 4. *)
    ( "r_to_l example 1" >:: fun _ ->
      assert_equal 4 (map_r_to_l "EKMFLGDQVZNTOWYHXUSPAIBRCJ" 'A' 0) );
  ]

let map_l_to_r_tests = []

let map_refl_tests = []

let map_plug_tests = []

let cipher_char_tests = [
    (* Identity machine: no plugs, no rotors, identity reflector. *)
    ( "identity machine" >:: fun _ ->
      assert_equal 'A'
        (cipher_char
           {
             refl = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
             rotors = [];
             plugboard = [];
           }
           'A') );
  ]

let step_tests = []

let cipher_tests = []


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
           cipher_tests;
         ]

let () = run_test_tt_main suite
