open Core.Std

include Nothing.Replace_polymorphic_compare

module Rational : sig
  type t [@@deriving bin_io, compare, sexp, typerep]

  include Floatable.S with type t := t
  include Identifiable.S with type t := t
  include Comparable.With_zero with type t := t

  val create : numerator:int -> denominator:int -> t

  val of_int : int -> t
  val to_int_exact_exn : t -> int
  val to_int_round : t -> [ `Up | `Down | `Nearest | `Zero ] -> int

  val zero : t
  val one : t
  val minus_one : t
  val (+) : t -> t -> t
  val (-) : t -> t -> t
  val ( * ) : t -> t -> t
  val (/) : t -> t -> t
  val neg : t -> t
  val (~-) : t -> t
  val abs : t -> t
  val min_value : t
  val max_value : t
end = struct
  let gcd x y =
    let rec gcd' ~smaller ~larger =
      if Int.equal smaller 0
      then larger
      else gcd' ~smaller:(larger mod smaller) ~larger:smaller
    in
    if Int.(<) x y
    then gcd' ~smaller:x ~larger:y
    else gcd' ~smaller:x ~larger:y
  ;;

  let lcm x y = (x / gcd x y) * y

  module T = struct
    type t =
      { numerator : int
      ; denominator : int
      }
    [@@deriving bin_io, sexp, typerep]

    let with_common_denominator x y =
      let denominator = lcm x.denominator y.denominator in
      let x_numerator = x.numerator * (denominator / x.denominator) in
      let y_numerator = y.numerator * (denominator / y.denominator) in
      (x_numerator, y_numerator, denominator)
    ;;

    let zero = { numerator = 0; denominator = 1 }

    let compare x y =
      let (x_numerator, y_numerator, _) = with_common_denominator x y in
      Int.compare x_numerator y_numerator
    ;;

    let hash t =
      Int.hash t.numerator lxor Int.hash t.denominator
    ;;

    let to_string t =
      Int.to_string t.numerator ^/ Int.to_string t.denominator
    ;;

    let of_string t =
      let (numerator_string, denominator_string) =
        String.lsplit2_exn t ~on:'/'
      in
      { numerator = Int.of_string numerator_string
      ; denominator = Int.of_string denominator_string
      }
    ;;

    let module_name = "Rational"
  end

  include T
  include Identifiable.Make (T)
  include Comparable.Validate_with_zero (T)

  let create ~numerator ~denominator =
    if Int.equal denominator 0
    then begin
      raise_s
        [%message
          "attempt to create a rational number with denominator of zero"]
    end
    else begin
      let sign =
        if not (Bool.equal (Int.is_negative numerator) (Int.is_negative denominator))
        then -1
        else 1
      in
      let abs_numerator = Int.abs numerator in
      let abs_denominator = Int.abs denominator in
      let gcd = gcd abs_numerator abs_denominator in
      { numerator = sign * (abs_numerator / gcd)
      ; denominator = abs_denominator / gcd
      }
    end
  ;;

  let of_float _f = failwith "???unimpl"
  let to_float _f = failwith "???unimpl"

  let of_int i =
    { numerator = i; denominator = 1 }
  ;;

  let to_int_exact_exn t =
    if Int.equal t.denominator 1
    then t.numerator
    else begin
      raise_s
        [%message
          "Rational.to_int_exn called on non-integer"
            ~rational:(t : t)]
    end
  ;;

  let to_int_round t dir =
    Int.round ~dir t.numerator ~to_multiple_of:t.denominator
  ;;

  let zero = { numerator = 0; denominator = 1 }
  let one = { numerator = 1; denominator = 1 }
  let minus_one = { numerator = -1; denominator = 1 }

  let (+) x y =
    let (x_numerator, y_numerator, denominator) = with_common_denominator x y in
    { numerator = x_numerator + y_numerator
    ; denominator
    }
  ;;

  let (-) x y =
    let (x_numerator, y_numerator, denominator) = with_common_denominator x y in
    { numerator = x_numerator - y_numerator
    ; denominator
    }
  ;;

  let ( * ) x y =
    let numerator = x.numerator * y.numerator in
    let denominator = x.denominator * y.denominator in
    let gcd = gcd numerator denominator in
    { numerator = numerator / gcd
    ; denominator = denominator / gcd
    }
  ;;

  let ( / ) x y =
    let open Int.O in
    let numerator =
      x.numerator * y.denominator
      * (if Int.is_negative y.numerator
         then -1
         else 1)
    in
    let denominator = Int.abs (x.denominator * y.numerator) in
    if denominator = 0
    then raise_s [%message "attempt to divide by zero"]
    else begin
      let gcd = gcd numerator denominator in
      { numerator = numerator / gcd
      ; denominator = denominator / gcd
      }
    end
  ;;

  let neg { numerator; denominator } =
    { numerator = -numerator; denominator }
  ;;

  let (~-) = neg

  let abs { numerator; denominator } =
    { numerator = Int.abs numerator; denominator }
  ;;

  let min_value =
    { numerator = Int.min_value; denominator = 1 }
  ;;

  let max_value =
    { numerator = Int.max_value; denominator = 1 }
  ;;
end

module Typ = struct
  module T = struct
    type t =
      | Normal
      | Fighting
      | Flying
      | Poison
      | Ground
      | Rock
      | Bug
      | Ghost
      | Steel
      | Fire
      | Water
      | Grass
      | Electric
      | Psychic
      | Ice
      | Dragon
      | Dark
      | Fairy
    [@@deriving compare, enumerate, sexp]

    let to_int = function
      | Normal -> 0
      | Fighting -> 1
      | Flying -> 2
      | Poison -> 3
      | Ground -> 4
      | Rock -> 5
      | Bug -> 6
      | Ghost -> 7
      | Steel -> 8
      | Fire -> 9
      | Water -> 10
      | Grass -> 11
      | Electric -> 12
      | Psychic -> 13
      | Ice -> 14
      | Dragon -> 15
      | Dark -> 16
      | Fairy -> 17
    ;;

    let hash t = Int.hash (to_int t)
  end

  include T
  include Comparable.Make (T)
  include Hashable.Make (T)

  let one_half = Rational.create ~numerator:1 ~denominator:2

  let matchup_gen2 ~attacking ~defending =
    match (attacking, defending) with
    | (Normal, (Rock | Steel)) -> one_half
    | (Normal, Ghost) -> Rational.zero
    | (Normal, _) -> Rational.one
    | (Fighting, (Normal | Rock | Steel | Ice | Dark)) -> Rational.of_int 2
    | (Fighting, (Flying | Poison | Bug | Psychic)) -> one_half
    | (Fighting, Ghost) -> Rational.zero
    | (Fighting, _) -> Rational.one
    | (Flying, (Fighting | Bug | Grass)) -> Rational.of_int 2
    | (Flying, (Rock | Steel | Electric)) -> one_half
    | (Flying, _) -> Rational.one
    | (Poison, Grass) -> Rational.of_int 2
    | (Poison, (Poison | Ground | Rock | Ghost)) -> one_half
    | (Poison, Steel) -> Rational.zero
    | (Poison, _) -> Rational.one
    | (Ground, (Poison | Rock | Steel | Fire | Electric)) -> Rational.of_int 2
    | (Ground, (Bug | Grass)) -> one_half
    | (Ground, Flying) -> Rational.zero
    | (Ground, _) -> Rational.one
    | (Rock, (Flying | Bug | Fire | Ice)) -> Rational.of_int 2
    | (Rock, (Fighting | Ground | Steel)) -> one_half
    | (Rock, _) -> Rational.one
    | (Bug, (Grass | Psychic | Dark)) -> Rational.of_int 2
    | (Bug, (Poison | Fighting | Flying | Ghost | Steel | Fire)) -> one_half
    | (Bug, _) -> Rational.one
    | (Ghost, Ghost) -> Rational.of_int 2
    | (Ghost, (Steel | Dark)) -> one_half
    | (Ghost, (Normal | Psychic)) -> Rational.zero
    | (Ghost, _) -> Rational.one
    | (Steel, (Rock | Ice)) -> Rational.of_int 2
    | (Steel, (Steel | Fire | Water | Electric)) -> one_half
    | (Steel, _) -> Rational.one
    | (Fire, (Bug | Steel | Grass | Ice)) -> Rational.of_int 2
    | (Fire, (Rock | Fire | Water | Dragon)) -> one_half
    | (Fire, _) -> Rational.one
    | (Water, (Ground | Rock | Fire)) -> Rational.of_int 2
    | (Water, (Water | Grass | Dragon)) -> one_half
    | (Water, _) -> Rational.one
    | (Grass, (Ground | Rock | Water)) -> Rational.of_int 2
    | (Grass, (Flying | Poison | Bug | Steel | Fire | Grass | Dragon)) -> one_half
    | (Grass, _) -> Rational.one
    | (Electric, (Flying | Water)) -> Rational.of_int 2
    | (Electric, (Grass | Electric | Dragon)) -> one_half
    | (Electric, Ground) -> Rational.zero
    | (Electric, _) -> Rational.one
    | (Psychic, (Fighting | Poison)) -> Rational.of_int 2
    | (Psychic, (Steel | Psychic)) -> one_half
    | (Psychic, Dark) -> Rational.zero
    | (Psychic, _) -> Rational.one
    | (Ice, (Flying | Ground | Grass | Dragon)) -> Rational.of_int 2
    | (Ice, (Steel | Water | Ice | Fire)) -> one_half
    | (Ice, _) -> Rational.one
    | (Dragon, Dragon) -> Rational.of_int 2
    | (Dragon, Steel) -> one_half
    | (Dragon, _) -> Rational.one
    | (Dark, (Ghost | Psychic)) -> Rational.of_int 2
    | (Dark, (Fighting | Steel | Dark)) -> one_half
    | (Dark, _) -> Rational.one
    | _ -> Rational.one
  ;;

  let matchup ~attacking ~defending =
    match (attacking, defending) with
    | (Normal, (Rock | Steel)) -> one_half
    | (Normal, Ghost) -> Rational.zero
    | (Normal, _) -> Rational.one
    | (Fighting, (Normal | Rock | Steel | Ice | Dark)) -> Rational.of_int 2
    | (Fighting, (Flying | Poison | Bug | Psychic | Fairy)) -> one_half
    | (Fighting, Ghost) -> Rational.zero
    | (Fighting, _) -> Rational.one
    | (Flying, (Fighting | Bug | Grass)) -> Rational.of_int 2
    | (Flying, (Rock | Steel | Electric)) -> one_half
    | (Flying, _) -> Rational.one
    | (Poison, (Grass | Fairy)) -> Rational.of_int 2
    | (Poison, (Poison | Ground | Rock | Ghost)) -> one_half
    | (Poison, Steel) -> Rational.zero
    | (Poison, _) -> Rational.one
    | (Ground, (Poison | Rock | Steel | Fire | Electric)) -> Rational.of_int 2
    | (Ground, (Bug | Grass)) -> one_half
    | (Ground, Flying) -> Rational.zero
    | (Ground, _) -> Rational.one
    | (Rock, (Flying | Bug | Fire | Ice)) -> Rational.of_int 2
    | (Rock, (Fighting | Ground | Steel)) -> one_half
    | (Rock, _) -> Rational.one
    | (Bug, (Grass | Psychic | Dark)) -> Rational.of_int 2
    | (Bug, (Poison | Fighting | Flying | Ghost | Steel | Fire | Fairy)) -> one_half
    | (Bug, _) -> Rational.one
    | (Ghost, (Ghost | Psychic)) -> Rational.of_int 2
    | (Ghost, Dark) -> one_half
    | (Ghost, Normal) -> Rational.zero
    | (Ghost, _) -> Rational.one
    | (Steel, (Rock | Ice | Fairy)) -> Rational.of_int 2
    | (Steel, (Steel | Fire | Water | Electric)) -> one_half
    | (Steel, _) -> Rational.one
    | (Fire, (Bug | Steel | Grass | Ice)) -> Rational.of_int 2
    | (Fire, (Rock | Fire | Water | Dragon)) -> one_half
    | (Fire, _) -> Rational.one
    | (Water, (Ground | Rock | Fire)) -> Rational.of_int 2
    | (Water, (Water | Grass | Dragon)) -> one_half
    | (Water, _) -> Rational.one
    | (Grass, (Ground | Rock | Water)) -> Rational.of_int 2
    | (Grass, (Flying | Poison | Bug | Steel | Fire | Grass | Dragon)) -> one_half
    | (Grass, _) -> Rational.one
    | (Electric, (Flying | Water)) -> Rational.of_int 2
    | (Electric, (Grass | Electric | Dragon)) -> one_half
    | (Electric, Ground) -> Rational.zero
    | (Electric, _) -> Rational.one
    | (Psychic, (Fighting | Poison)) -> Rational.of_int 2
    | (Psychic, (Steel | Psychic)) -> one_half
    | (Psychic, Dark) -> Rational.zero
    | (Psychic, _) -> Rational.one
    | (Ice, (Flying | Ground | Grass | Dragon)) -> Rational.of_int 2
    | (Ice, (Steel | Water | Ice | Fire)) -> one_half
    | (Ice, _) -> Rational.one
    | (Dragon, Dragon) -> Rational.of_int 2
    | (Dragon, Steel) -> one_half
    | (Dragon, Fairy) -> Rational.zero
    | (Dragon, _) -> Rational.one
    | (Dark, (Ghost | Psychic)) -> Rational.of_int 2
    | (Dark, (Fighting | Dark | Fairy)) -> one_half
    | (Dark, _) -> Rational.one
    | (Fairy, (Fighting | Dragon | Dark)) -> Rational.of_int 2
    | (Fairy, (Poison | Steel | Fire)) -> one_half
    | (Fairy, _) -> Rational.one
  ;;
end

module Base_stats = struct
  type t =
    { health : int
    ; attack : int
    ; defense : int
    ; special_attack : int
    ; special_defense : int
    ; speed : int
    }
  [@@deriving sexp]

  let total
        { health
        ; attack
        ; defense
        ; special_attack
        ; special_defense
        ; speed
        } =
    health
    + attack
    + defense
    + special_attack
    + special_defense
    + speed
  ;;
end


module Pokemon : sig
  type t = private
    { name : string
    ; type1 : Typ.t
    ; type2 : Typ.t option
    ; base_stats : Base_stats.t
    }
  [@@deriving enumerate, sexp]

  include Comparable.S with type t := t
  include Hashable.S with type t := t

  val all_set : Set.t
  val find_by_name : string -> t option
  val find_by_name_exn : string -> t
  val all_with_type : Typ.t -> t list
  val all_with_type_combo : ?ignore_order:unit -> Typ.t -> Typ.t option -> t list
end = struct
  module T = struct
    type t =
      { name : string
      ; type1 : Typ.t
      ; type2 : Typ.t option
      ; base_stats : Base_stats.t
      }
    [@@deriving sexp]

    let compare t1 t2 = String.compare t1.name t2.name
    let hash t = String.hash t.name
  end

  include T
  include Comparable.Make (T)
  include Hashable.Make (T)

  let all_without_base_stats =
    let megas : (string * Typ.t * Typ.t option) list =
      [ ("Mega Venusaur", Grass, Some Poison)
      ; ("Mega Charizard X", Fire, Some Dragon)
      ; ("Mega Charizard Y", Fire, Some Flying)
      ; ("Mega Blastoise", Water, None)
      ; ("Mega Alakazam", Psychic, None)
      ; ("Mega Gengar", Ghost, Some Poison)
      ; ("Mega Kangaskhan", Normal, None)
      ; ("Mega Pinsir", Bug, Some Flying)
      ; ("Mega Gyarados", Water, Some Dark)
      ; ("Mega Aerodactyl", Rock, Some Flying)
      ; ("Mega Mewtwo X", Psychic, Some Fighting)
      ; ("Mega Mewtwo Y", Psychic, None)
      ; ("Mega Ampharos", Electric, Some Dragon)
      ; ("Mega Scizor", Bug, Some Steel)
      ; ("Mega Heracross", Bug, Some Fighting)
      ; ("Mega Houndoom", Dark, Some Fire)
      ; ("Mega Tyranitar", Rock, Some Dark)
      ; ("Mega Blaziken", Fire, Some Fighting)
      ; ("Mega Gardevoir", Psychic, Some Fairy)
      ; ("Mega Mawile", Steel, Some Fairy)
      ; ("Mega Aggron", Steel, None)
      ; ("Mega Medicham", Psychic, Some Fighting)
      ; ("Mega Manectric", Electric, None)
      ; ("Mega Banette", Ghost, None)
      ; ("Mega Absol", Dark, None)
      ; ("Mega Garchomp", Dragon, Some Ground)
      ; ("Mega Lucario", Fighting, Some Steel)
      ; ("Mega Abomasnow", Grass, Some Ice)
      ; ("Mega Beedrill", Bug, Some Poison)
      ; ("Mega Pidgeot", Normal, Some Flying)
      ; ("Mega Slowbro", Water, Some Psychic)
      ; ("Mega Steelix", Steel, Some Ground)
      ; ("Mega Sceptile", Grass, Some Dragon)
      ; ("Mega Swampert", Water, Some Ground)
      ; ("Mega Sableye", Dark, Some Ghost)
      ; ("Mega Sharpedo", Water, Some Dark)
      ; ("Mega Camerupt", Fire, Some Ground)
      ; ("Mega Altaria", Dragon, Some Fairy)
      ; ("Mega Glalie", Ice, None)
      ; ("Mega Salamence", Dragon, Some Flying)
      ; ("Mega Metagross", Steel, Some Psychic)
      ; ("Mega Latias", Dragon, Some Psychic)
      ; ("Mega Latios", Dragon, Some Psychic)
      ; ("Mega Rayquaza", Dragon, Some Flying)
      ; ("Mega Lopunny", Normal, Some Fighting)
      ; ("Mega Gallade", Psychic, Some Fighting)
      ; ("Mega Audino", Normal, Some Fairy)
      ; ("Mega Diancie", Rock, Some Fairy)
      ]
    in
    let sexps = Sexp.load_sexps "all_pokemon.sexp" in
    megas
    @ List.map sexps
        ~f:(fun sexp ->
          match [%of_sexp: string * Typ.t] sexp with
          | (name, type1) -> (name, type1, None)
          | exception e1 ->
            (match [%of_sexp: string * Typ.t * Typ.t] sexp with
             | (name, type1, type2) -> (name, type1, Some type2)
             | exception e2 ->
               Error.raise (Error.of_list [Error.of_exn e1; Error.of_exn e2])))
  ;;

  let base_stats_table =
    Sexp.load_sexps_conv_exn "base_stats.sexp"
      [%of_sexp: string * int * int * int * int * int * int]
    |> List.map
         ~f:(fun
              (name,
               health,
               attack,
               defense,
               special_attack,
               special_defense,
               speed) ->
              (name,
               { Base_stats.
                 health
               ; attack
               ; defense
               ; special_attack
               ; special_defense
               ; speed
               }))
    |> String.Table.of_alist_exn

  let all =
    List.map all_without_base_stats
      ~f:(fun (name, type1, type2) ->
        let base_stats =
          match Hashtbl.find base_stats_table name with
          | None ->
            raise_s [%message "no base stats found for pokemon" (name : string)]
          | Some base_stats -> base_stats
        in
        { name; type1; type2; base_stats })
  ;;

  let all_set = Set.of_list all

  let find_by_name =
    let table =
      String.Table.of_alist_exn
        (List.map all
           ~f:(fun pkmn -> (pkmn.name, pkmn)))
    in
    Hashtbl.find table
  ;;

  let find_by_name_exn name =
    match find_by_name name with
    | None -> raise_s [%message "no such pokemon" (name : string)]
    | Some t -> t
  ;;

  let () =
    List.iter (Hashtbl.keys base_stats_table)
      ~f:(fun name -> ignore (find_by_name_exn name))
  ;;

  let all_with_type =
    let table =
      List.map Typ.all
        ~f:(fun typ ->
          (typ,
           List.filter all
             ~f:(fun { type1; type2; _ } ->
               Typ.equal type1 typ
               || (match type2 with
                 | None -> false
                 | Some type2 -> Typ.equal type2 typ))))
      |> Typ.Table.of_alist_exn
    in
    Hashtbl.find_exn table
  ;;

  let all_with_type_combo =
    let table =
      List.map Typ.all
        ~f:(fun type1 ->
          (type1,
           (List.filter all
             ~f:(fun { type1 = type1'; type2 = type2'; _ } ->
               Typ.equal type1 type1'
               && Option.equal Typ.equal None type2'),
            List.map Typ.all
              ~f:(fun type2 ->
                (type2,
                 List.filter all
                   ~f:(fun { type1 = type1'; type2 = type2'; _ } ->
                     Typ.equal type1 type1'
                     && Option.equal Typ.equal (Some type2) type2')))
            |> Typ.Table.of_alist_exn)))
      |> Typ.Table.of_alist_exn
    in
    fun ?ignore_order type1 type2 ->
      match type2 with
      | None -> fst (Hashtbl.find_exn table type1)
      | Some type2 ->
        (match ignore_order with
         | None -> Hashtbl.find_exn (snd (Hashtbl.find_exn table type1)) type2
         | Some () ->
           Hashtbl.find_exn (snd (Hashtbl.find_exn table type1)) type2
           @ Hashtbl.find_exn (snd (Hashtbl.find_exn table type2)) type1)
  ;;

  (*
  let _gen1 =
    [ { name = "Venusaur"
      ; type1 = Grass
      ; type2 = Some Poison
      }
    ; { name = "Charizard"
      ; type1 = Fire
      ; type2 = Some Flying
      }
    ; { name = "Blastoise"
      ; type1 = Water
      ; type2 = None
      }
    ; { name = "Butterfree"
      ; type1 = Bug
      ; type2 = Some Flying
      }
    ; { name = "Beedrill"
      ; type1 = Bug
      ; type2 = Some Poison
      }
    ; { name = "Pidgeot"
      ; type1 = Normal
      ; type2 = Some Flying
      }
    ; { name = "Raticate"
      ; type1 = Normal
      ; type2 = None
      }
    ; { name = "Fearow"
      ; type1 = Normal
      ; type2 = Some Flying
      }
    ; { name = "Arbok"
      ; type1 = Poison
      ; type2 = None
      }
    ; { name = "Raichu"
      ; type1 = Electric
      ; type2 = None
      }
    ; { name = "Sandslash"
      ; type1 = Ground
      ; type2 = None
      }
    ; { name = "Nidoqueen"
      ; type1 = Poison
      ; type2 = Some Ground
      }
    ; { name = "Nidoking"
      ; type1 = Poison
      ; type2 = Some Ground
      }
    ; { name = "Clefable"
      ; type1 = Normal
      ; type2 = None
      }
    ; { name = "Ninetales"
      ; type1 = Fire
      ; type2 = None
      }
    ; { name = "Wigglytuff"
      ; type1 = Normal
      ; type2 = None
      }
    ; { name = "Golbat"
      ; type1 = Poison
      ; type2 = Some Flying
      }
    ; { name = "Vileplume"
      ; type1 = Grass
      ; type2 = Some Poison
      }
    ; { name = "Parasect"
      ; type1 = Bug
      ; type2 = Some Grass
      }
    ; { name = "Venomoth"
      ; type1 = Bug
      ; type2 = Some Poison
      }
    ; { name = "Dugtrio"
      ; type1 = Ground
      ; type2 = None
      }

    ; { name = "Persian"
      ; type1 = Normal
      ; type2 = None
      }
    ; { name = "Golduck"
      ; type1 = Water
      ; type2 = None
      }
    ; { name = "Primeape"
      ; type1 = Fighting
      ; type2 = None
      }
    ; { name = "Arcanine"
      ; type1 = Fire
      ; type2 = None
      }
    ; { name = "Poliwrath"
      ; type1 = Water
      ; type2 = Some Fighting
      }
    ; { name = "Alakazam"
      ; type1 = Psychic
      ; type2 = None
      }
    ; { name = "Machamp"
      ; type1 = Fighting
      ; type2 = None
      }
    ; { name = "Victreebell"
      ; type1 = Grass
      ; type2 = Some Poison
      }
    ; { name = "Tentacruel"
      ; type1 = Water
      ; type2 = Some Poison
      }
    ; { name = "Golem"
      ; type1 = Rock
      ; type2 = Some Ground
      }
    ; { name = "Rapidash"
      ; type1 = Fire
      ; type2 = None
      }
    ; { name = "Slowbro"
      ; type1 = Water
      ; type2 = Some Psychic
      }
    ; { name = "Magneton"
      ; type1 = Electric
      ; type2 = None
      }
    ; { name = "Farfetch'd"
      ; type1 = Normal
      ; type2 = Some Flying
      }
    ; { name = "Dodrio"
      ; type1 = Normal
      ; type2 = Some Flying
      }
    ; { name = "Dewgong"
      ; type1 = Water
      ; type2 = Some Ice
      }
    ; { name = "Muk"
      ; type1 = Poison
      ; type2 = None
      }
    ; { name = "Cloyster"
      ; type1 = Water
      ; type2 = Some Ice
      }
    ; { name = "Gengar"
      ; type1 = Ghost
      ; type2 = Some Poison
      }
    ; { name = "Onix"
      ; type1 = Rock
      ; type2 = Some Ground
      }
    ; { name = "Hypno"
      ; type1 = Psychic
      ; type2 = None
      }
    ; { name = "Kingler"
      ; type1 = Water
      ; type2 = None
      }
    ; { name = "Electrode"
      ; type1 = Electric
      ; type2 = None
      }

    ; { name = "Exeggutor"
      ; type1 = Grass
      ; type2 = Some Psychic
      }
    ; { name = "Marowak"
      ; type1 = Ground
      ; type2 = None
      }
    ; { name = "Hitmonlee"
      ; type1 = Fighting
      ; type2 = None
      }
    ; { name = "Hitmonchan"
      ; type1 = Fighting
      ; type2 = None
      }
    ; { name = "Lickitung"
      ; type1 = Normal
      ; type2 = None
      }
    ; { name = "Weezing"
      ; type1 = Poison
      ; type2 = None
      }
    ; { name = "Rhydon"
      ; type1 = Ground
      ; type2 = Some Rock
      }
    ; { name = "Chansey"
      ; type1 = Normal
      ; type2 = None
      }
    ; { name = "Tangela"
      ; type1 = Grass
      ; type2 = None
      }
    ; { name = "Kangaskhan"
      ; type1 = Normal
      ; type2 = None
      }
    ; { name = "Seadra"
      ; type1 = Water
      ; type2 = None
      }
    ; { name = "Seaking"
      ; type1 = Water
      ; type2 = None
      }
    ; { name = "Starmie"
      ; type1 = Water
      ; type2 = Some Ice
      }
    ; { name = "Mr. Mime"
      ; type1 = Psychic
      ; type2 = None
      }
    ; { name = "Scyther"
      ; type1 = Bug
      ; type2 = Some Flying
      }
    ; { name = "Jynx"
      ; type1 = Ice
      ; type2 = Some Psychic
      }
    ; { name = "Electabuzz"
      ; type1 = Electric
      ; type2 = None
      }
    ; { name = "Magmar"
      ; type1 = Fire
      ; type2 = None
      }
    ; { name = "Pinsir"
      ; type1 = Bug
      ; type2 = None
      }
    ; { name = "Tauros"
      ; type1 = Normal
      ; type2 = None
      }
    ; { name = "Gyarados"
      ; type1 = Water
      ; type2 = Some Flying
      }
    ; { name = "Lapras"
      ; type1 = Water
      ; type2 = Some Ice
      }
    ; { name = "Ditto"
      ; type1 = Normal
      ; type2 = None
      }
    ; { name = "Vaporeon"
      ; type1 = Water
      ; type2 = None
      }
    ; { name = "Jolteon"
      ; type1 = Electric
      ; type2 = None
      }
    ; { name = "Flareon"
      ; type1 = Fire
      ; type2 = None
      }
    ; { name = "Porygon"
      ; type1 = Normal
      ; type2 = None
      }
    ; { name = "Omastar"
      ; type1 = Rock
      ; type2 = Some Water
      }
    ; { name = "Kabutops"
      ; type1 = Rock
      ; type2 = Some Water
      }
    ; { name = "Aerodactyl"
      ; type1 = Rock
      ; type2 = Some Flying
      }
    ; { name = "Snorlax"
      ; type1 = Normal
      ; type2 = None
      }
    ; { name = "Articuno"
      ; type1 = Ice
      ; type2 = Some Flying
      }
    ; { name = "Zapdos"
      ; type1 = Electric
      ; type2 = Some Flying
      }
    ; { name = "Moltres"
      ; type1 = Fire
      ; type2 = Some Flying
      }
    ; { name = "Dragonite"
      ; type1 = Dragon
      ; type2 = Some Flying
      }
    ; { name = "Mewtwo"
      ; type1 = Psychic
      ; type2 = None
      }
    ; { name = "Mew"
      ; type1 = Psychic
      ; type2 = None
      }
    ]
  ;;*)

end

module Analysis = struct
  let effectiveness
        ~attack_type
        ~defender:({ type1; type2; _ } : Pokemon.t) =
    Rational.( * )
      (Typ.matchup ~attacking:attack_type ~defending:type1)
      (match type2 with
       | None -> Rational.one
       | Some type2 -> Typ.matchup ~attacking:attack_type ~defending:type2)
  ;;

  let effective ~attack_type ~defender =
    Rational.(>) (effectiveness ~attack_type ~defender) Rational.one
  ;;

  let can_beat (pkmn1 : Pokemon.t) (pkmn2 : Pokemon.t) =
    (effective ~attack_type:pkmn1.type1 ~defender:pkmn2
     || (match pkmn1.type2 with
       | None -> false
       | Some type2 -> effective ~attack_type:type2 ~defender:pkmn2))
    && not
         (effective ~attack_type:pkmn2.type1 ~defender:pkmn1
          || (match pkmn2.type2 with
            | None -> false
            | Some type2 -> effective ~attack_type:type2 ~defender:pkmn1))
  ;;

  let filter_beatable pkmn_to_beat pkmn =
    Pokemon.Set.of_list (List.filter ~f:(can_beat pkmn) pkmn_to_beat)
  ;;

  let filter_beatable_by_team pkmn_to_beat team =
    Pokemon.Set.union_list (List.map team ~f:(filter_beatable pkmn_to_beat))
  ;;

  (* ??? Don't include duplicate types combinations *)
  let all_beatable =
    let table =
      List.map Pokemon.all
        ~f:(fun pkmn -> (pkmn, filter_beatable Pokemon.all pkmn))
      |> Pokemon.Table.of_alist_exn
    in
    Hashtbl.find_exn table
  ;;

  let all_beatable_by_team team =
    Pokemon.Set.union_list (List.map team ~f:all_beatable)
  ;;

  let how_to_beat team pkmn =
    List.filter team
      ~f:(fun team_member -> can_beat team_member pkmn)
  ;;

  type team_analysis =
    { beatable : Pokemon.Set.t
    ; num_beatable : int
    ; not_beatable : Pokemon.Set.t
    ; num_not_beatable : int
    ; advise : (string -> Pokemon.t list) sexp_opaque
    }
  [@@deriving sexp_of]

  let analyze_team team =
    let beatable = all_beatable_by_team team in
    let not_beatable = Set.diff Pokemon.all_set beatable in
    let advise name = how_to_beat team (Pokemon.find_by_name_exn name) in
    { beatable
    ; num_beatable = Set.length beatable
    ; not_beatable
    ; num_not_beatable = Set.length not_beatable
    ; advise
    }
  ;;

  let find_good_teams ~fixed_team_part potential_pokemon ~variable_part_size =
    let rec choose_n n l =
      match n with
      | 0 -> [[]]
      | _ ->
        (match l with
         | [] -> []
         | x::xs ->
           List.map ~f:(fun l -> x::l) (choose_n (n - 1) xs)
           @ choose_n n xs)
    in
    let variable_parts = choose_n variable_part_size potential_pokemon in
    let fixed_part_size = List.length fixed_team_part in
    let potential_teams =
      if Int.(>) fixed_part_size variable_part_size
      then List.map variable_parts ~f:(fun team -> team @ fixed_team_part)
      else List.map variable_parts ~f:(fun team -> fixed_team_part @ team)
    in
    let teams_with_beatables =
      List.map potential_teams
        ~f:(fun team ->
          let beatable = all_beatable_by_team team in
          (team, Pokemon.Set.length beatable, beatable))
    in
    List.fold teams_with_beatables
      ~init:(0, [])
      ~f:(fun (best_count_so_far, teams_that_achieve_it) (team, count, _) ->
        if Int.(<) count best_count_so_far
        then (best_count_so_far, teams_that_achieve_it)
        else if Int.equal count best_count_so_far
        then (best_count_so_far, team :: teams_that_achieve_it)
        else (count, [team]))
  ;;
end

open Analysis

let beating_cycles_of_size n =
  let rec choose2 = function
    | [] -> []
    | x::xs -> List.map ~f:(fun y -> (x, y)) xs @ choose2 xs
  in
  let is_cycle l =
    let len = List.length l in
    List.for_all
      ~f:(fun ((i, pi), (j, pj)) ->
        if Int.equal (j - i) 1
        then can_beat pi pj
        else if Int.equal i 0 && Int.equal j (len - 1)
        then can_beat pj pi
        else not (can_beat pi pj || can_beat pj pi))
      (choose2 (List.mapi ~f:(fun i x -> (i, x)) l))
  in
  let rec insert_everywhere x = function
    | [] -> [[x]]
    | [y] -> [[x; y]]
    | y::z::ys ->
      (x :: y :: z :: ys)
      :: List.rev_map ~f:(fun l -> y :: l) (insert_everywhere x (z::ys))
  in
  let rec potential_cycles l n =
    match n with
    | 0 -> [[]]
    | _ ->
      (match l with
       | [] -> []
       | x::xs ->
         List.concat
           (List.rev_map ~f:(insert_everywhere x) (potential_cycles xs (n - 1)))
         @ potential_cycles xs n)
  in
  List.filter ~f:is_cycle (potential_cycles Pokemon.all n)
;;

(* ??? Fix gen1 types
let team1 : Pokemon.t list =
  List.map ~f:Pokemon.find_by_name_exn
    [ "Mewtwo"
    ; "Zapdos"
    ; "Chansey"
    ; "Rhydon"
    ; "Arcanine"
    ; "Poliwrath"
    ]
;;

let can_beat1 = team_can_beat gen1_pkmn team1
let total1 = List.length gen1_pkmn
let count1 = Pokemon.Set.length can_beat1
let cannot_beat1 =
  Pokemon.Set.to_list (Pokemon.Set.diff (Pokemon.Set.of_list gen1_pkmn) can_beat1)
;;
*)


(* Uncomment this to be prompted to decide between pokemon
let sorted_by_preference =
  List.sort gen1_pkmn
    ~cmp:(fun pkmn1 pkmn2 ->
      printf "%s"
        (Sexp.to_string (sexp_of_pokemon pkmn1) ^ " vs. " ^ Sexp.to_string (sexp_of_pokemon pkmn2));
      let ans = read_line () in
      match int_of_string ans with
        | 1 -> 1
        | 2 -> -1)
*)

let uber_nonlegendary =
  List.map ~f:Pokemon.find_by_name_exn
    [ "Shield Forme Aegislash"
    ; "Blaziken"
    ; "Mega Blaziken"
    ; "Mega Gengar"
    ; "Greninja"
    ; "Mega Kangaskhan"
    ; "Mega Lucario"
    ; "Mega Mawile"
    ; "Mega Salamence"
    ]
;;

let ou_nonlegendary =
  List.map ~f:Pokemon.find_by_name_exn
    [ "Altaria"
    ; "Dragonite"
    ; "Mega Altaria"
    ; "Azumarill"
    ; "Bisharp"
    ; "Breloom"
    ; "Chansey"
    ; "Lopunny"
    ; "Charizard"
    ; "Mega Charizard X"
    ; "Mega Charizard Y"
    ; "Talonflame"
    ; "Clefable"
    ; "Sylveon"
    ; "Conkeldurr"
    ; "Excadrill"
    ; "Ferrothorn"
    ; "Gallade"
    ; "Mega Gallade"
    ; "Garchomp"
    ; "Mega Garchomp"
    ; "Gardevoir"
    ; "Mega Gardevoir"
    ; "Gengar"
    ; "Gliscor"
    ; "Gothitelle"
    ; "Gyarados"
    ; "Mega Gyarados"
    ; "Mega Lopunny"
    ; "Magnezone"
    ; "Mamoswine"
    ; "Mandibuzz"
    ; "Manectric"
    ; "Mega Manectric"
    ; "Metagross"
    ; "Mega Metagross"
    ; "Wash Rotom"
    ; "Sableye"
    ; "Scizor"
    ; "Mega Scizor"
    ; "Serperior"
    ; "Skarmory"
    ; "Slowbro"
    ; "Mega Slowbro"
    ; "Starmie"
    ; "Tyranitar"
    ; "Mega Tyranitar"
    ; "Venusaur"
    ; "Mega Venusaur"
    ]
;;

let ou_teams = []

let team2 =
  List.map ~f:Pokemon.find_by_name_exn
    [ "Blaziken"
    ; "Shield Forme Aegislash"
    ; "Greninja"; "Muk"; "Glaceon"
    ; "Gliscor"
    ; "Mega Gardevoir"
    ; "Manectric"
    ]
;;

(*let good_teams = find_good_teams (uber_nonlegendary @ ou_nonlegendary) ~team_size:4*)

let gen6_good_teams =
  find_good_teams ~fixed_team_part:[] team2 ~variable_part_size:4
;;

let team2_analysis = analyze_team team2

let team3 =
  List.map ~f:Pokemon.find_by_name_exn
    [ "Greninja"
    ; "Silvally" ; "Electivire"
    ; "Kommo-o"
    ; "Arcanine"
    ; "Alolan Dugtrio"
    ; "Alolan Ninetales"
    ]
;;

let good_alola_pokemon =
  List.map ~f:Pokemon.find_by_name_exn
    [ "Decidueye"
    ; "Incineroar"
    ; "Primarina"
    ; "Toucannon"
    ; "Gumshoos"
    ; "Alolan Raticate"
    ; "Butterfree"
    ; "Ledian"
    ; "Ariados"
    ; "Alolan Raichu"
    ; "Vikavolt"
    ; "Sudowoodo"
    ; "Blissey"
    ; "Snorlax"
    ; "Slowking"
    ; "Pelipper"
    ; "Alakazam"
    ; "Alolan Persian"
    ; "Magnezone"
    ; "Alolan Muk"
    ; "Arcanine"
    ; "Hypno"
    ; "Hariyama"
    ; "Smeargle"
    ; "Crabominable"
    ; "Gengar"
    ; "Drifblim"
    ; "Mismagius"
    ; "Crobat"
    ; "Alolan Dugtrio"
    ; "Fearow"
    ; "Braviary"
    ; "Mandibuzz"
    ; "Primeape"
    ; "Delibird"
    ; "Oricorio"
    ; "Ribombee"
    ; "Lilligant"
    ; "Whimsicott"
    ; "Golduck"
    ; "Gyarados"
    ; "Whiscash"
    ; "Machamp"
    ; "Gigalith"
    ; "Carbink"
    ; "Sableye"
    ; "Midday Form Lycanroc"
    ; "Spinda"
    ; "Tentacruel"
    ; "Lumineon"
    ; "Wishiwashi"
    ; "Luvdisc"
    ; "Corsola"
    ; "Toxapex"
    ; "Cloyster"
    ; "Salamence"
    ; "Stoutland"
    ; "Vaporeon"
    ; "Jolteon"
    ; "Flareon"
    ; "Espeon"
    ; "Umbreon"
    ; "Leafeon"
    ; "Glaceon"
    ; "Sylveon"
    ; "Mudsdale"
    ; "Wigglytuff"
    ; "Tauros"
    ; "Miltank"
    ; "Masquerain"
    ; "Araquanid"
    ; "Lurantis"
    ; "Shiinotic"
    ; "Parasect"
    ; "Poliwrath"
    ; "Politoed"
    ; "Seaking"
    ; "Milotic"
    ; "Alomomola"
    ; "Talonflame"
    ; "Salazzle"
    ; "Alolan Marowak"
    ; "Kangaskhan"
    ; "Magmortar"
    ; "Bewear"
    ; "Tsareena"
    ; "Comfey"
    ; "Pinsir"
    ; "Oranguru"
    ; "Passimian"
    ; "Goodra"
    ; "Castform"
    ; "Golisopod"
    ; "Starmie"
    ; "Palossand"
    ; "Rampardos"
    ; "Bastiodon"
    (*; "Archeops"*)
    ; "Carracosta"
    ; "Trevenant"
    ; "Probopass"
    ; "Pyukumuku"
    ; "Lanturn"
    ; "Silvally"
    ; "Garbodor"
    ; "Skarmory"
    ; "Ditto"
    ; "Clefable"
    ; "Minior"
    ; "Metagross"
    ; "Porygon-Z"
    ; "Pangoro"
    ; "Komala"
    ; "Torkoal"
    ; "Turtonator"
    ; "Togedemaru"
    ; "Electivire"
    ; "Alolan Golem"
    ; "Krookodile"
    ; "Flygon"
    ; "Garchomp"
    ; "Klefki"
    ; "Mimikyu"
    ; "Bruxish"
    ; "Drampa"
    ; "Absol"
    ; "Glalie"
    ; "Froslass"
    ; "Weavile"
    ; "Alolan Sandslash"
    ; "Alolan Ninetales"
    ; "Vanilluxe"
    ; "Granbull"
    ; "Gastrodon"
    ; "Relicanth"
    ; "Dhelmise"
    ; "Sharpedo"
    ; "Wailord"
    ; "Lapras"
    ; "Alolan Exeggutor"
    ; "Kommo-o"
    ; "Emolga"
    ; "Scizor"
    ; "Honchkrow"
    ; "Lucario"
    ; "Dragonite"
    ; "Aerodactyl"
    ]
  |> List.filter
       ~f:(fun pokemon ->
         Int.(>=) (Base_stats.total pokemon.Pokemon.base_stats) 530)
;;

let team3_analysis =
  analyze_team team3
;;

let single_battle_team =
  find_good_teams ~fixed_team_part:[] team3 ~variable_part_size:3
;;

let double_battle_team =
  find_good_teams ~fixed_team_part:[] team3 ~variable_part_size:4
;;

let team_eddie =
  List.map ~f:Pokemon.find_by_name_exn
    [ "Machamp"
    ; "Snorlax"
    ; "Tyranitar"
    ; "Exeggutor"
    ; "Ampharos"
    ]
;;
