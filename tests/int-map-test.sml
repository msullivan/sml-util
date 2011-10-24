structure HighBit =
struct
  local
      open Word
  in
  fun highestBit1' (x,m) =
      let val x' = andb (x,notb (m-0w1))
          fun highb (x,m) =
              if x=m then m else highb (andb (x,notb m),m+m)
      in highb (x',m) end
  fun highestBit1 x = highestBit1' (x,0w1)
  fun highestBit2 x =
      let val x = orb (x, >>(x, 0wx1))
          val x = orb (x, >>(x, 0wx2))
          val x = orb (x, >>(x, 0wx4))
          val x = orb (x, >>(x, 0wx8))
          val x = orb (x, >>(x, 0wx10))
      in xorb (x, >>(x, 0wx1)) end

  (* XXX: UNSAFE: It's faster, and I do my own bounds check. *)
  structure V = (*Unsafe.*)Vector

  val table = Vector.tabulate (65336, highestBit2 o fromInt)
  fun highestBit3 x =
      if x < 0w65336 then
          V.sub (table, toInt x)
      else <<(V.sub (table, toInt (>>(x,0w16))), 0w16)
  end
end

structure HighBitTest =
struct
  fun time f x =
      let val start = Time.now ()
          val _ = f x
          val stop = Time.now ()
      in Time.toMicroseconds (Time.- (stop, start)) end

  fun test f num =
      let fun test_bit 0w0 = ()
            | test_bit n = (f n; test_bit (n-0w1))
          fun loop1 0 = ()
            | loop1 n = (test_bit num; loop1 (n-1))
          val iters = 1000
      in loop1 iters end
end

signature WORD_ORD_MAP = ORD_MAP where type Key.ord_key = word
signature INT_ORD_MAP = ORD_MAP where type Key.ord_key = int

(* This is a signature solely to reduce debug spew. *)
signature MAP_TEST =
sig
    structure M : INT_ORD_MAP
    val id : 'a -> 'a
    val rand : unit -> word
    val numbers : int -> int list
    val rands : int -> int list
    val test_adds : M.Key.ord_key list -> string M.map
    val test_lookups : string M.map -> M.Key.ord_key list -> M.Key.ord_key list -> bool
    val test2 : ('a -> M.Key.ord_key list) -> ('a -> M.Key.ord_key list) -> 'a -> (M.Key.ord_key list * M.Key.ord_key list) option
    val test : ('a -> M.Key.ord_key list) -> ('a -> M.Key.ord_key list) -> 'a -> bool
    val test_correctness : unit -> bool
    val time : ('a -> 'b) -> 'a -> IntInf.int
    val test_speed : ('a -> M.Key.ord_key list)
                     -> 'a -> {insert:IntInf.int, lookup:IntInf.int}
    val test_speed_seq : int -> {insert:IntInf.int, lookup:IntInf.int}
    val test_speed_rand : int -> {insert:IntInf.int, lookup:IntInf.int}
    val test_speed_both : int
                          -> {rand:{insert:IntInf.int, lookup:IntInf.int},
                              seq:{insert:IntInf.int, lookup:IntInf.int}}
end

functor MapTestFn (M : INT_ORD_MAP) : MAP_TEST =
struct
  structure M = M
  fun id x = x

  (* mlton seems to have a bug where it raises Fail during codegen when
   * trying to compile this. just hardcode the seed. *)
  val rand = (Word.fromLargeWord o Word31.toLargeWord) o
             Rand.mkRandom (*0wx1badd00d*)
                 (Word31.fromLargeInt (Time.toMicroseconds (Time.now ())))

  fun intersect' l1 l2 = List.filter (fn i => not (Util.contains i l2)) l1

  fun numbers n = List.tabulate (n, id)
  fun rands n = List.tabulate (n, fn _ => Word.toInt (rand () mod 0w20000))

  fun test_adds l = foldl (fn (i, M) => M.insert (M, i, Int.toString i)) M.empty l
  fun remove' (i, S) = (Util.first (M.remove (S, i)) handle e => S)
  fun test_removes S l = foldl remove' S l

  fun test_lookups M lin lout =
      let
          fun match_in x =
              case M.find (M, x) of SOME x' => Int.toString x = x'
                                  | NONE => false
          fun match_out x = not (isSome (M.find (M, x)))
      in
          List.all match_in lin andalso List.all match_out lout
      end

  fun test2 f g n =
      let val l = f n
          val missing = g n
          val l' = intersect' l missing
          val M = test_adds l
          val M' = test_removes M missing
      in if test_lookups M' l' missing then NONE else SOME (l, missing) end
  fun test f g n =
      let val l = f n
          val missing = g n
          val l' = intersect' l missing
          val M = test_adds l
          val M' = test_removes M missing
      in test_lookups M' l' missing end

  fun test_correctness () =
      let val test_seq = test numbers rands
          val test_random = test rands rands

          val sizes = [1, 2, 4, 8, 15, 14, 32, 1024, 10000, 100000]
          val seq_results = map test_seq sizes
          val rand_results = map test_random sizes
          val all_good = List.all id seq_results andalso List.all id rand_results
      in all_good end

  fun time f x =
      let val start = Time.now ()
          val _ = f x
          val stop = Time.now ()
      in Time.toMicroseconds (Time.- (stop, start)) end

  fun test_speed f n =
      let val data = f n
          val M = test_adds data
          fun loop1 0 = ()
            | loop1 n = (test_adds data; loop1 (n-1))
          fun loop2 0 = ()
            | loop2 n = (test_lookups M data []; loop2 (n-1))
          val iters = 1000
      in {insert=time loop1 iters, lookup=time loop2 iters} end
  val test_speed_seq = test_speed numbers
  val test_speed_rand = test_speed rands
  fun test_speed_both n = {seq=test_speed_seq n, rand=test_speed_rand n}

end

structure WordKey =
struct
  type ord_key = word
  val compare = Word.compare
end
structure IntKey =
struct
  type ord_key = int
  val compare = Int.compare
end

structure SplayMap = SplayMapFn(IntKey)
structure SplayMapTest = MapTestFn(SplayMap)

structure RedBlackMap = RedBlackMapFn(IntKey)
structure RedBlackMapTest = MapTestFn(RedBlackMap)

structure BinaryMap = BinaryMapFn(IntKey)
structure BinaryMapTest = MapTestFn(BinaryMap)

structure IntMapTest = MapTestFn(IntMap)

fun test_all n = [SplayMapTest.test_speed_both n,
                  RedBlackMapTest.test_speed_both n,
                  BinaryMapTest.test_speed_both n,
                  IntMapTest.test_speed_both n]

fun test size =
    let (*val results = test_all size*)
        val results = [IntMapTest.test_speed_both size]
        val is = LargeInt.toString
        fun print_test {seq={insert=insert_seq, lookup=lookup_seq},
                        rand={insert=insert_rand, lookup=lookup_rand}} =
                        print (is insert_seq ^ "\t" ^ is lookup_seq ^ "\t" ^
                               is insert_rand ^ "\t" ^ is lookup_rand ^ "\n")
        val () = List.app print_test results
    in () end

fun main name args =
    if length args < 1 then () else test (valOf (Int.fromString (hd args)))

val _ = main (CommandLine.name ()) (CommandLine.arguments ())
