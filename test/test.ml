open OUnit2
open Enigma

let index_tests = [
  ("index A" >:: fun _ -> assert_equal 0  (index 'A'));
  ("index B" >:: fun _ -> assert_equal 1  (index 'B'));
  ("index C" >:: fun _ -> assert_equal 2  (index 'C'));
  ("index Z" >:: fun _ -> assert_equal 25 (index 'Z'));
  ("index O" >:: fun _ -> assert_equal 14 (index 'O'));
]

let map_r_to_l_tests = [
  ("r_to_l identity wiring" >:: fun _ ->
    assert_equal 0  (map_r_to_l "ABCDEFGHIJKLMNOPQRSTUVWXYZ" 'A' 0 ));
  ("r_to_l rotorI top A" >:: fun _ ->
    assert_equal 4  (map_r_to_l "EKMFLGDQVZNTOWYHXUSPAIBRCJ" 'A' 0 ));
  ("r_to_l rotorI top B" >:: fun _ ->
    assert_equal 9  (map_r_to_l "EKMFLGDQVZNTOWYHXUSPAIBRCJ" 'B' 0 ));
  ("r_to_l rotorIII wraps both" >:: fun _ ->
    assert_equal 17 (map_r_to_l "BDFHJLCPRTXVZNYEIWGAKMUSQO" 'O' 14));
]

(*
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
*)


let suite =
  "enigma test suite"
  >::: List.flatten
         [
           index_tests;
           map_r_to_l_tests;
(*         map_l_to_r_tests; *)
(*         map_refl_tests; *)
(*         map_plug_tests; *)
(*         cipher_char_tests; *)
(*         step_tests; *)
(*         cipher_tests; *)
         ]

let () = run_test_tt_main suite
