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
  ("r_to_l identity wiring top A" >:: fun _ ->
    assert_equal 0  (map_r_to_l "ABCDEFGHIJKLMNOPQRSTUVWXYZ" 'A' 0 ));
  ("r_to_l rotorI top A" >:: fun _ ->
    assert_equal 4  (map_r_to_l "EKMFLGDQVZNTOWYHXUSPAIBRCJ" 'A' 0 ));
  ("r_to_l rotorI top B" >:: fun _ ->
    assert_equal 9  (map_r_to_l "EKMFLGDQVZNTOWYHXUSPAIBRCJ" 'B' 0 ));
  ("r_to_l rotorIII wraps both" >:: fun _ ->
    assert_equal 17 (map_r_to_l "BDFHJLCPRTXVZNYEIWGAKMUSQO" 'O' 14));
]

let map_l_to_r_tests = [
  ("l_to_r identity wiring top A" >:: fun _ ->
    assert_equal 0  (map_l_to_r "ABCDEFGHIJKLMNOPQRSTUVWXYZ" 'A' 0 ));
  ("l_to_r rotorI top A" >:: fun _ ->
    assert_equal 20 (map_l_to_r "EKMFLGDQVZNTOWYHXUSPAIBRCJ" 'A' 0));
  ("l_to_r rotorI top B" >:: fun _ ->
    assert_equal 21 (map_l_to_r "EKMFLGDQVZNTOWYHXUSPAIBRCJ" 'B' 0 ));
  ("l_to_r rotorI top F input_pos 10" >:: fun _ ->
    assert_equal 14 (map_l_to_r "EKMFLGDQVZNTOWYHXUSPAIBRCJ" 'F' 10));
]


let suite =
  "enigma test suite"
  >::: List.flatten
         [
           index_tests;
           map_r_to_l_tests;
           map_l_to_r_tests;
(*         map_refl_tests; *)
(*         map_plug_tests; *)
(*         cipher_char_tests; *)
(*         step_tests; *)
(*         cipher_tests; *)
         ]

let () = run_test_tt_main suite
