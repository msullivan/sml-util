signature AMB =
sig
    (* Non-deterministically select an element from a list *)
    val amb : 'a list -> 'a
    (* Given a non-deterministic computation, return all possible
     * results. *)
    val collect : (unit -> 'a) -> 'a list
    (* Given a non-deterministic computation, return the first possible
     * result, and cut off any other possible results from consideration.
     * I think this is related to Prolog's cut. *)
    val collect1 : (unit -> 'a) -> 'a option
end

structure Amb :> AMB =
struct
   open SMLofNJ.Cont

   val state : unit cont ref =
       ref (callcc (fn escape : unit cont cont =>
                       (callcc (fn k => throw escape k);
                        raise Fail "amb backtracking failed at top level")))

   fun amb [] = throw (!state) ()
     | amb (x::xs) =
       let val old = !state
       in callcc (fn escape =>
                     (callcc (fn k => (state := k; throw escape x));
                      state := old;
                      amb xs))
       end

   (* run a computation without changing the backtracking points *)
   fun encapsulate f =
       let val old = !state
       in f () before state := old end

   (* I got this collect implementation from Joshua Wise. My
    * original one was uglier and relied on the internals of amb. *)
   fun collect f =
       let val xs = ref [] in
           if amb [true, false]
           then (xs := f () :: !xs; amb []) else rev (!xs)
       end

   fun collect1 f =
       encapsulate
           (fn () => if amb [true, false] then SOME (f ()) else NONE)

end

local
    open Amb
in

fun test0 () =
    let
        val x = amb [1, 2, 3, 4, 5]
        val _ = if x <> 4 then amb nil else 0
    in
        x
    end

fun test1 () =
    let
        val x = amb [ 2, 3, 4, 5 ]
        val y = amb [ "a", "aaaaa", "aaaaaaa", "aa" ]
    in
        if x <> (size y) then amb nil else y
    end

fun factor_test l1 l2 n () =
    let
        val x = amb l1
        val y = amb l2
        val _ = if x*y <> n then amb nil else ()
    in
        (x, y)
    end

val test2 = factor_test [1, 2, 3] [4, 5, 6]     10
val test3 = factor_test [1, 2, 3] [4, 5, 6, 10] 10
val test4 = factor_test [1, 2, 3] [4, 5, 6, 10] 13

end
