(* Test the recursive set thing with pure sets
 * (sets containing only sets) *)

structure PureListSetTest =
struct
  structure SetCore = ListSetCore (*****)
  datatype pset = S of pset SetCore.set
  fun cmp (S a, S b) = SetCore.compare cmp (a, b)
  structure Key = struct type ord_key = pset val compare = cmp end
  structure PSet = ListSetRecFn(Key) (*****)
end

structure PureBinarySetTest =
struct
  structure SetCore = BinarySetCore (*****)
  datatype pset = S of pset SetCore.set
  fun cmp (S a, S b) = SetCore.compare cmp (a, b)
  structure Key = struct type ord_key = pset val compare = cmp end
  structure PSet = BinarySetRecFn(Key) (*****)
end

structure PureSplaySetTest =
struct
  structure SetCore = SplaySetCore (*****)
  datatype pset = S of pset SetCore.set
  fun cmp (S a, S b) = SetCore.compare cmp (a, b)
  structure Key = struct type ord_key = pset val compare = cmp end
  structure PSet = SplaySetRecFn(Key) (*****)
end

structure PureRedBlackSetTest =
struct
  structure SetCore = RedBlackSetCore (*****)
  datatype pset = S of pset SetCore.set
  fun cmp (S a, S b) = SetCore.compare cmp (a, b)
  structure Key = struct type ord_key = pset val compare = cmp end
  structure PSet = RedBlackSetRecFn(Key) (*****)
end
