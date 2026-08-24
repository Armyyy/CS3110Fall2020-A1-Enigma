(* Implement each function below. Delete the [failwith] and write the
   real definition. Types and specs live in enigma.mli -- read them first,
   let the type drive the implementation. *)

(* Step 3 *)
let index c = Char.code c - Char.code 'A'
let letter idx = Char.chr (idx + Char.code 'A')
let wrap x = ((x mod 26) + 26) mod 26

(* Step 5 *)
(*
0 2 4 6 8 10  14  18  22 25 (contact position)
| | | | | |   |   |   |  |
v v v v v v   v   v   v  v
BDFHJLCPRTXVZNYEIWGAKMUSQO (rotor's wiring)
  ^           ^
  |           |
  |           offset = index top_letter
  |                  = index 'O'
  |                  = 14
  |
  contact_out = (offset + input_pos) mod 26
              = (14 + 14) mod 26
              = 2

  output = (index wiring.[contact_out] - offset) mod 26
         = (index wiring.[2] - 14) mod 26
         = (index 'F' - 14) mod 26
         = (5 - 14) mod 26
         = (-9) mod 26
         = 17
*)
let map_r_to_l wiring top_letter input_pos =
  let offset = top_letter |> index in
  let contact_out = offset + input_pos |> wrap in
  index wiring.[contact_out] - offset |> wrap

(*
0 2 4 6 8 10  14  18  22 25 (contact position)
| | | | | |   |   |   |  |
v v v v v v   v   v   v  v
EKMFLGDQVZNTOWYHXUSPAIBRCJ (rotor's wiring)
ABCDEFGHIJKLMNOPQRSTUVWXYZ (identity wiring)
               ^
               |_________________
                                 |
  offset = index top_letter      |
        = index 'F'              |
          = 5                    |
   ______________________________|
  |
  v
  contact_out = (offset + input_pos) mod 26
              = (5 + 10) mod 26
              = 15

  output = (String.index wiring identity_wiring.[contact_out] - offset) mod 26
         = (String.index wiring identity_wiring.[15] - 5) mod 26
         = (String.index wiring 'P' - 5) mod 26
         = (String.index wiring 'P' - 5) mod 26
         = (19 - 5) mod 26
         = 14
*)
let map_l_to_r wiring top_letter input_pos =
  let offset = top_letter |> index in
  let contact_out = offset + input_pos |> wrap in
  String.index wiring (contact_out |> letter) - offset |> wrap

(* Step 6 *)
let map_refl wiring input_pos = map_r_to_l wiring 'A' input_pos

(* Step 7 *)
let rec map_plug plugs c = match plugs with
  | [] -> c
  | (fst, snd)::t ->
    if fst = c then snd
    else if snd = c then fst
    else map_plug t c

type rotor = {
  wiring : string;
  turnover : char;
}

type oriented_rotor = {
  rotor : rotor;
  top_letter : char;
}

type config = {
  refl : string;
  rotors : oriented_rotor list;
  plugboard : (char * char) list;
}

(*
  Step 8.
  Hint: write two recursive helpers first
    map_rotors_r_to_l : oriented_rotor list -> int -> int
    map_rotors_l_to_r : oriented_rotor list -> int -> int
  then look for the common helper hiding inside both.
*)

(*
  [rotor_traversal f input_pos rotors] threads [input_pos] through every
  rotor in [rotors], in list order, mapping it with [f] at each one.
  The rotor list comes last so that callers can pipe into it.
*)
let rotor_traversal f input_pos rotors = let rec loop acc = function
  | [] -> acc
  | {rotor = {wiring = w; _}; top_letter = top}::t
    -> loop (f w top acc) t
  in loop input_pos rotors

(* Current enters from the right, but [rotors] is stored leftmost first. *)
let map_rotors_r_to_l rotors input_pos = rotors
  |> List.rev
  |> rotor_traversal map_r_to_l input_pos

let map_rotors_l_to_r rotors input_pos = rotors
  |> rotor_traversal map_l_to_r input_pos

(*
  The path a current takes through the machine, in order:
  plugboard, rotors right to left, reflector, rotors left to right,
  and back out through the plugboard.
*)
let cipher_char config c = c
  |> map_plug config.plugboard
  |> index
  |> map_rotors_r_to_l config.rotors
  |> map_refl config.refl
  |> map_rotors_l_to_r config.rotors
  |> letter
  |> map_plug config.plugboard

(* Step 9 *)
let next_char c = letter (wrap (index c + 1))
let is_notch o_router = o_router.top_letter = o_router.rotor.turnover

let rotate rotors =
  let rec loop previous_is_notch acc = function
    | [] -> acc
    | h::t ->
      let not_left_most = t <> [] in
      let current_is_notch = is_notch h in
      if (previous_is_notch || (current_is_notch && not_left_most)) then loop
        (current_is_notch)
        ({ h with top_letter = h.top_letter |> next_char }::acc) t
      else loop (current_is_notch) (h::acc) t
  in loop true [] (rotors |> List.rev)

let step config = {
  config with
  rotors = config.rotors |> rotate
}

(* Step 10 *)

(*
  The machine steps first, then enciphers under the new configuration,
  which is carried forward to the next letter.
*)
let step_and_encrypt (out, config) char = let stepped = config |> step in
  (char |> cipher_char stepped) :: out, stepped

let cipher config s = s
  |> String.fold_left step_and_encrypt ([], config)
  |> fst
  |> List.rev
  |> List.to_seq
  |> String.of_seq

let _hours_worked = 9.9

(*
  ________________________________________
  | commit hash | hours used (approximate) |
  |-------------|--------------------------|
  | aa5cbc7     | 1.5                      |
  | 1c96e63     | 0.5                      |
  | acd87fa     | 0.8                      |
  | 569b73a     | 0.4                      |
  | 668e47b     | 0.3                      |
  | 94ca43b     | 1.5                      |
  | 4974d8e     | 0.2                      |
  | bc39e1d     | 2.0                      |
  | 0d27a7e     | 2.0                      |
  | ea68839     | 0.7                      |
  | UNKNOWN     | X.X                      |
  |_____________|__________________________|
*)
