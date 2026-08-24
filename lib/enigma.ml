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
  let offset = index top_letter in
  let contact_out = (offset + input_pos) mod 26 in
  let output = (index wiring.[contact_out] - offset) in
  wrap output

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
  let offset = index top_letter in
  let contact_out = (offset + input_pos) mod 26 in
  let output = String.index wiring (letter contact_out) - offset in
  wrap output

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

(* Step 8.
   Hint: write two recursive helpers first
     map_rotors_r_to_l : oriented_rotor list -> int -> int
     map_rotors_l_to_r : oriented_rotor list -> int -> int
   then look for the common helper hiding inside both. *)

let rotor_traversal rotors input_pos f = let rec loop acc = function
  | [] -> acc
  | {rotor = {wiring = w; _}; top_letter = top}::t
    -> loop (f w top acc) t
  in loop input_pos rotors

let map_rotors_r_to_l rotors input_pos = let reversed = List.rev rotors in
  rotor_traversal reversed input_pos map_r_to_l

let map_rotors_l_to_r rotors input_pos =
  rotor_traversal rotors input_pos map_l_to_r

let cipher_char config c =
  let mapped_c = map_plug config.plugboard c in
  let r_to_l_out = map_rotors_r_to_l config.rotors (index mapped_c) in
  let reflected = map_refl config.refl r_to_l_out in
  let l_to_r_out = map_rotors_l_to_r config.rotors (reflected) in
  map_plug config.plugboard (letter l_to_r_out)

(* Step 9 *)
let step _config = failwith "step: Unimplemented"

(* Step 10 *)
let cipher _config _s = failwith "cipher: Unimplemented"
