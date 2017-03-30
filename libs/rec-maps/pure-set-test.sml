(* Test the recursive set thing with pure sets
 * (sets containing only sets) *)

signature PURE_SET_BASE =
sig
    structure PSet : ORD_SET
    val S : PSet.set -> PSet.item
    val unS : PSet.item -> PSet.set
end

structure PureListSetTest : PURE_SET_BASE =
struct
  structure SetCore = ListSetCore (*****)
  datatype pset = S of pset SetCore.set
  fun unS (S a) = a
  fun cmp (S a, S b) = SetCore.compare cmp (a, b)
  structure Key = struct type ord_key = pset val compare = cmp end
  structure PSet = ListSetRecFn(Key) (*****)
end

structure PureBinarySetTest : PURE_SET_BASE =
struct
  structure SetCore = BinarySetCore (*****)
  datatype pset = S of pset SetCore.set
  fun unS (S a) = a
  fun cmp (S a, S b) = SetCore.compare cmp (a, b)
  structure Key = struct type ord_key = pset val compare = cmp end
  structure PSet = BinarySetRecFn(Key) (*****)
end

structure PureSplaySetTest : PURE_SET_BASE =
struct
  structure SetCore = SplaySetCore (*****)
  datatype pset = S of pset SetCore.set
  fun unS (S a) = a
  fun cmp (S a, S b) = SetCore.compare cmp (a, b)
  structure Key = struct type ord_key = pset val compare = cmp end
  structure PSet = SplaySetRecFn(Key) (*****)
end

structure PureRedBlackSetTest : PURE_SET_BASE =
struct
  structure SetCore = RedBlackSetCore (*****)
  datatype pset = S of pset SetCore.set
  fun unS (S a) = a
  fun cmp (S a, S b) = SetCore.compare cmp (a, b)
  structure Key = struct type ord_key = pset val compare = cmp end
  structure PSet = RedBlackSetRecFn(Key) (*****)
end

(********)

functor PureSetTest(PS : PURE_SET_BASE) =
struct
  open PS
  structure P = PSet
  infix \/ /\

  (* Wrappers *)
  val empty = P.empty
  fun member (s, x) = P.member (s, S x)
  val (op \/) = P.union
  val (op /\) = P.intersection
  fun ` l = P.fromList (map S l)
  fun bigunion s = P.foldr (fn (x, s) => unS x \/ s) empty s
  fun bigintersection s =
    (case P.find (fn _ => true) s of
         NONE => empty
       | SOME start => P.foldr (fn (x, s) => unS x /\ s) (unS start) s)
  fun filter p s = P.filter (fn x => p (unS x)) s
  val equal = P.equal

  fun fmti x = fmt (unS x)
  and fmt s = "{" ^ String.concatWith ", " (map fmti (P.listItems s)) ^ "}"

  (**** operations on sets of sets ****)

  (* construct a natural number! *)
  fun nat 0 = empty
    | nat n =
      let val s = nat (n-1)
      in s \/ `[s] end

  fun implies (p, q) = not p orelse q

  (* construct an ordered pair *)
  fun pair (x, y) = `[`[x], `[x, y]]
  fun fst p = bigunion (bigintersection p)
  fun snd p =
    let val (cupP, capP) = (bigunion p, bigintersection p)
    in bigunion (filter (fn x => equal (cupP, capP) orelse
                                 not (member (capP, x)))
                        cupP)
    end
end

structure ListTest = PureSetTest(PureListSetTest)
structure BinaryTest = PureSetTest(PureBinarySetTest)
structure SplayTest = PureSetTest(PureSplaySetTest)
structure RedBlackTest = PureSetTest(PureRedBlackSetTest)
