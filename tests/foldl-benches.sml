fun addTuple (x, y) = x + y
fun addCurry  x  y  = x + y

signature FOLDL =
sig
  val sum : int list -> int
end

structure FoldlPair =
struct
  fun foldl f z [] = z
    | foldl f z (x::xs) = foldl f (f (x, z)) xs

  fun sum xs = foldl addTuple 0 xs
end

structure FoldlPairSilly =
struct
  fun foldl f z [] = z
    | foldl f z (x::xs) =
      let val pair = (x, z)
      in foldl f (f pair) xs end

  fun sum xs = foldl addTuple 0 xs
end

structure FoldlCurry =
struct
  fun foldl f z [] = z
    | foldl f z (x::xs) = foldl f (f x z) xs

  fun sum xs = foldl addCurry 0 xs
end

structure FoldlPairNest =
struct
  fun foldl f z xs =
      let fun loop z [] = z
            | loop z (x::xs) = loop (f (x, z)) xs
      in loop z xs end

  fun sum xs = foldl addTuple 0 xs
end

structure FoldlPairNest2 =
struct
  fun foldl f z xs =
      let fun loop (l, z) =
              case l of [] => z
                      | (x::xs) => loop (xs, f (x, z))
      in loop (xs, z) end

  fun sum xs = foldl addTuple 0 xs
end


structure FoldlCurryNest =
struct
  fun foldl f z xs =
      let fun loop z [] = z
            | loop z (x::xs) = loop (f x z) xs
      in loop z xs end

  fun sum xs = foldl addCurry 0 xs
end

structure Tests =
struct
  fun add l x = l := x :: (!l)
  val names : string list ref = ref []
  val benchmarks : (int -> IntInf.int) list ref = ref []
end

functor TestFun (structure F : FOLDL val name : string) =
struct
  structure F = F
  val name = name
  val () = Tests.add Tests.names name

  val is = Int.toString
  fun id x = x

  fun time f x =
      let val start = Time.now ()
          val _ = f x
          val stop = Time.now ()
      in Time.toMicroseconds (Time.- (stop, start)) end

  fun test_speed m =
      let val l = List.tabulate (m, fn x => x)
          val () = MLton.GC.collect ()

(*          val () = if F.fact 5 <> 120 then print (name ^ ": anus!\n") else ()*)
          fun loop1 0 = ()
            | loop1 n = (F.sum l; loop1 (n-1))
          val iters = 5000
          val _ = loop1 iters
      in time loop1 iters end
  val () = Tests.add Tests.benchmarks test_speed
end

structure T = TestFun(structure F = FoldlPair val name = "pair")
structure T = TestFun(structure F = FoldlPairSilly val name = "pair2")
structure T = TestFun(structure F = FoldlCurry val name = "curry")

structure T = TestFun(structure F = FoldlPairNest val name = "pair_nest")
structure T = TestFun(structure F = FoldlPairNest2 val name = "pair_nest2")
structure T = TestFun(structure F = FoldlCurryNest val name = "curry_nest")


(* Replace the Tests structure with a less hacky one *)
structure TestsLol = Tests
structure Tests =
struct
  local
      fun fixup l = rev (!l)
  in
  val names = fixup Tests.names
  val benchmarks = fixup Tests.benchmarks
  end
end

(* Stolen from from SML/NJ lib because I was too
 * lazy to make a .mlb to import smlnj-lib to test with mlton *)
fun sort (op > : 'a * 'a -> bool) ls = let
    fun merge([],ys) = ys
      | merge(xs,[]) = xs
      | merge(x::xs,y::ys) =
        if x > y then y::merge(x::xs,ys) else x::merge(xs,y::ys)
    fun mergepairs(ls as [l], k) = ls
      | mergepairs(l1::l2::ls,k) =
        if k mod 2 = 1 then l1::l2::ls
        else mergepairs(merge(l1,l2)::ls, k div 2)
      | mergepairs _ = raise Fail "ListSort.sort"
    fun nextrun(run,[])    = (rev run,[])
      | nextrun(run,x::xs) = if x > hd run then nextrun(x::run,xs)
                             else (rev run,x::xs)
    fun samsorting([], ls, k)    = hd(mergepairs(ls,0))
      | samsorting(x::xs, ls, k) = let
            val (run,tail) = nextrun([x],xs)
        in samsorting(tail, mergepairs(run::ls,k+1), k+1)
        end
in
    case ls of [] => [] | _ => samsorting(ls, [], 0)
end


(* Right pad a string to a certain length. Always add at least one space. *)
fun pad n s =
    let fun pad' n s = if String.size s >= n then s else pad' n (s^" ")
    in pad' (n-1) (s^" ") end

fun test n =
    let fun run f = f n
        val results = ListPair.zip (Tests.names, map run Tests.benchmarks)
        val results' = sort (fn ((_, x), (_, y)) => x > y) results
        fun print_test (name, time) =
            print (pad 14 name ^ LargeInt.toString time ^ "\n")
        val () = app print_test results'
    in () end

val fs = valOf o Int.fromString
fun main _ [n] = test (fs n)
  | main _ _ = ()

val _ = main (CommandLine.name ()) (CommandLine.arguments ())
