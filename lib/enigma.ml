(* Implement each function below. Delete the [failwith] and write the
   real definition. Types and specs live in enigma.mli -- read them first,
   let the type drive the implementation. *)

(* Step 3 *)
let index c = Char.code c - Char.code 'A'

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
  let output = (index wiring.[contact_out] - offset) mod 26 in
  if output < 0 then output + 26 else output


let map_l_to_r _wiring _top_letter _input_pos =
  failwith "map_l_to_r: Unimplemented"

(* Step 6 *)
let map_refl _wiring _input_pos = failwith "map_refl: Unimplemented"

(* Step 7 *)
let map_plug _plugs _c = failwith "map_plug: Unimplemented"

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
let cipher_char _config _c = failwith "cipher_char: Unimplemented"

(* Step 9 *)
let step _config = failwith "step: Unimplemented"

(* Step 10 *)
let cipher _config _s = failwith "cipher: Unimplemented"
