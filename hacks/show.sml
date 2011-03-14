(* In poly/ml, we can hook the pretty printer for arbitrary
 * monomorphic types by creating a new exception and formatting it with
 * exnMessage. 
 * It doesn't work in SML/NJ or mlton, though... *)

signature SHOW =
sig
  type t
  val show : t -> string
end

functor ShowFn(type t) : SHOW =
struct
  type t = t
  exception A of t
  (* The first two characters of the string are "A ", which we need to
   * discard. *)
  fun show x = String.extract (exnMessage (A x), 2, NONE)
end

(* Examples *)
fun println s = print (s ^ "\n")

structure IntPairShow = ShowFn(type t = int * int)
val () = println (IntPairShow.show (5, 1))

datatype 'a tree = Empty | Node of ('a * 'a tree * 'a tree)
structure IntTreeShow = ShowFn(type t = int tree)

val t = Node (7, Node (1, Empty, Empty), Node (42, Empty, Empty))
val () = println (IntTreeShow.show t)
