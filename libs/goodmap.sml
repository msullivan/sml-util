(* A modified map and set with some extra utility functions.
   One of the major things I wanted was the ability to map from
   sets into maps. *)

signature GOOD_MAP =
sig
  include ORD_MAP
  val delete : 'a map -> Key.ord_key -> 'a map
  val delete' : 'a map -> Key.ord_key -> 'a map

  val search: ('a map * Key.ord_key) -> 'a

  val format : (Key.ord_key -> string) -> ('a -> string) -> 'a map -> string

  val has : 'a map -> Key.ord_key -> bool

  (* These are just curried versions of common functions with shorter names. *)
  val bind : 'a map -> Key.ord_key -> 'a -> 'a map
  val bind' : 'a map -> Key.ord_key * 'a -> 'a map
  val look : 'a map -> Key.ord_key -> 'a option
  val look' : 'a map -> Key.ord_key -> 'a
  (* This is a version of look' that raises a different exception because
   * debugging is impossible in SML and I am a sloppy programmer and use
   * look' all over the fucking place. *)
  val look'' : 'a map -> Key.ord_key -> 'a
  val count : 'a map -> int
  val elems : 'a map -> 'a list
  val elemsi : 'a map -> (Key.ord_key * 'a) list
  val keys : 'a map -> Key.ord_key list
end

signature GOOD_SET =
sig
  include ORD_SET
  structure Map : GOOD_MAP
  sharing Map.Key = Key

  val delete' : (set * Key.ord_key) -> set

  val mapPartialToMap : (Key.ord_key -> 'a option) -> set -> 'a Map.map
  val mapToMap : (Key.ord_key -> 'a) -> set -> 'a Map.map

  val format' : string -> (Key.ord_key -> string) -> set -> string
  val format : (Key.ord_key -> string) -> set -> string

  val removeList : (set * Key.ord_key list) -> set

  (* These are just curried versions of common functions with shorter names. *)
  val addlist : set -> Key.ord_key list -> set
  val has : set -> Key.ord_key -> bool
  val ins : set -> Key.ord_key -> set
  val remove : set -> Key.ord_key -> set
  val remove' : set -> Key.ord_key -> set
  val count : set -> int
  val items : set -> Key.ord_key list
end

signature SET_MAP =
sig
  structure S1 : GOOD_SET
  structure S2 : GOOD_SET
  val mapPartial : (S1.Key.ord_key -> S2.Key.ord_key option) -> S1.set -> S2.set
  val map : (S1.Key.ord_key -> S2.Key.ord_key) -> S1.set -> S2.set
end

functor SetMapFn (structure AS1 : GOOD_SET structure AS2 : GOOD_SET) : SET_MAP =
struct
  structure S1 = AS1
  structure S2 = AS2

  fun mapPartial f s =
      S1.foldl
          (fn (k, s) => case f k of NONE => s
                                  | SOME v => S2.add (s, v))
          S2.empty s

  fun map f s = mapPartial (SOME o f) s
end

functor GoodMapFn' (M : ORD_MAP) : GOOD_MAP =
struct
  structure M = M
  open M

  fun delete m k = let val (m', _) = remove (m, k) in m' end
  fun delete' m k = delete m k
                       handle NotFound => m

  fun search (m, k) = case find (m, k) of SOME v => v
                                        | NONE => raise LibBase.NotFound

  fun has m k = isSome (find (m, k))

  fun bind t s x = insert (t, s, x)
  fun bind' t (s, x) = insert (t, s, x)
  fun look t s = find (t, s)
  fun look' t s = search (t, s)
  fun look'' t s = look' t s handle NotFound => raise Fail "it is failing here, asshole"
  fun count t = numItems t
  fun elems t = listItems t
  fun elemsi t = listItemsi t
  fun keys t = listKeys t

  fun format f g m = "{" ^
                     Print.fmt_list' ", " (fn (k, v) => (f k) ^ ": " ^ (g v)) (elemsi m) ^
                     "}"
end

functor GoodMapFn (K : ORD_KEY) : GOOD_MAP =
struct
  structure SM = SplayMapFn(K)
  structure GM = GoodMapFn'(SM)
  open GM
end

functor GoodMapWordFn (K : WORDABLE) : GOOD_MAP =
struct
  structure WM = WordMapFn(K)
  structure GM = GoodMapFn'(WM)
  open GM
end

functor GoodSetFn (M : GOOD_MAP) : GOOD_SET =
struct
  structure Map = M
  structure S = SplaySetFn(Map.Key)
  open S

  fun delete' (m, k) = delete (m, k)
                       handle NotFound => m

  fun mapPartialToMap f s =
      foldl
          (fn (k, m) => case f k of NONE => m
                                  | SOME v => Map.insert (m, k, v))
          Map.empty s

  fun mapToMap f s = mapPartialToMap (SOME o f) s

  fun removeList (S, ls) = List.foldl (fn (x, S) => delete' (S, x)) S ls

  fun format' s f S =  Print.fmt_list' s f (listItems S)
  fun format f S = "{" ^ (format' ", " f S) ^ "}"

  fun addlist S l = addList (S, l)
  fun has S s = member (S, s)
  fun ins S s = add (S, s)
  fun remove S s = delete (S, s)
  fun remove' S s = delete' (S, s)
  val count = numItems
  val items = listItems
end
