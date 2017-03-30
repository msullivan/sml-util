(* A test of recursive sets inspired by one of the puzzles in the 2006
 * ICFP programming contest, which featured an adventure game where
 * items could be viewed as propositions in a logic in which implication
 * was from a set of props to another prop. *)
structure RecSetTest =
struct
  structure SetCore = BinarySetCore (*****)

  (* Propositions are either atomic or an implication from a set
   * props to a prop.
   * A ::= P
   *     | {A, ..., A} -o A
   *)
  datatype Prop = Atom of string
                | Imp of Prop SetCore.set * Prop

  fun prop_compare (Atom n1, Atom n2) = String.compare (n1, n2)
    | prop_compare (Imp (ps, p), Imp (qs, q)) =
      (case SetCore.compare prop_compare (ps, qs) of
           EQUAL => prop_compare (p, q)
         | x => x)
    | prop_compare (Atom _, Imp _) = LESS
    | prop_compare (Imp _, Atom _) = GREATER

  structure Key = struct
    type ord_key = Prop
    val compare = prop_compare
  end
  structure PropSet = BinarySetRecFn(Key) (*****)

  val a = Atom "a"
  val b = Atom "b"
  val c = Atom "c"

  val a_imp_b = Imp (PropSet.fromList [a], b)
  val c' = Imp (PropSet.fromList [a, a_imp_b], c)
end
