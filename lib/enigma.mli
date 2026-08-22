(** An implementation of the Enigma machine. *)

(** [index c] is the 0-based index of [c] in the alphabet.
    Requires: [c] is an uppercase letter in A..Z. *)
val index : char -> int

(** [map_r_to_l wiring top_letter input_pos] is the left-hand output position
    at which current appears when current enters at right-hand input position
    [input_pos] to a rotor whose wiring specification is given by [wiring].
    The orientation of the rotor is given by [top_letter], which is the
    top letter appearing to the operator in the rotor's window.
    Requires: [wiring] is a valid wiring specification,
      [top_letter] is in 'A'..'Z', and
      [input_pos] is in 0..25. *)
val map_r_to_l : string -> char -> int -> int

(** [map_l_to_r] computes the same function as [map_r_to_l], except
    for current flowing left to right. *)
val map_l_to_r : string -> char -> int -> int

(** [map_refl wiring input_pos] is the output position at which current appears
    when current enters at input position [input_pos] to a reflector whose
    wiring specification is given by [wiring].
    Requires: [wiring] is a valid reflector wiring specification, and
      [input_pos] is in 0..25. *)
val map_refl : string -> int -> int

(** [map_plug plugs c] is the letter to which [c] is transformed
    by the plugboard [plugs].
    Requires: [plugs] is a valid plugboard, and [c] is in 'A'..'Z'. *)
val map_plug : (char * char) list -> char -> char

(** A [rotor] is a rotor of the Enigma machine. *)
type rotor = {
  wiring : string;
      (** A valid wiring specification. *)
  turnover : char;
      (** The turnover of the rotor, which must be an uppercase letter. *)
}

(** An [oriented_rotor] is a rotor that is installed on the spindle
    hence has a top letter. *)
type oriented_rotor = {
  rotor : rotor;
      (** The rotor. *)
  top_letter : char;
      (** The top letter showing on the rotor. *)
}

(** A [config] is a configuration of the Enigma machine. *)
type config = {
  refl : string;
      (** A valid reflector wiring specification. *)
  rotors : oriented_rotor list;
      (** The rotors as they are installed on the spindle from left to right.
          The order of the list is the same as the order on the spindle:
          the head of the list is the leftmost rotor. *)
  plugboard : (char * char) list;
      (** A valid plugboard. *)
}

(** [cipher_char config c] is the letter to which the Enigma machine
    ciphers input [c] when it is in configuration [config].
    Requires: [config] is a valid configuration, and [c] is in 'A'..'Z'. *)
val cipher_char : config -> char -> char

(** [step config] is the new configuration to which the Enigma machine
    transitions when it steps beginning in configuration [config].
    Requires: [config] is a valid configuration. *)
val step : config -> config

(** [cipher config s] is the string to which [s] enciphers
    when the Enigma machine begins in configuration [config].
    Requires: [config] is a valid configuration, and [s] contains only
      uppercase letters. *)
val cipher : config -> string -> string
