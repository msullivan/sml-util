(* Test the recursive set thing with pure maps
 * (maps mapping maps to maps) *)

structure PureListMapTest =
struct
  structure MapCore = ListMapCore (*****)
  datatype pmap = M of (pmap, pmap) MapCore.map
  fun cmp (M a, M b) = MapCore.collate cmp cmp (a, b)
  structure Key = struct type ord_key = pmap val compare = cmp end
  structure PMap = ListMapRecFn(Key) (*****)
end

structure PureBinaryMapTest =
struct
  structure MapCore = BinaryMapCore (*****)
  datatype pmap = M of (pmap, pmap) MapCore.map
  fun cmp (M a, M b) = MapCore.collate cmp cmp (a, b)
  structure Key = struct type ord_key = pmap val compare = cmp end
  structure PMap = BinaryMapRecFn(Key) (*****)
end

structure PureSplayMapTest =
struct
  structure MapCore = SplayMapCore (*****)
  datatype pmap = M of (pmap, pmap) MapCore.map
  fun cmp (M a, M b) = MapCore.collate cmp cmp (a, b)
  structure Key = struct type ord_key = pmap val compare = cmp end
  structure PMap = SplayMapRecFn(Key) (*****)
end

structure PureRedBlackMapTest =
struct
  structure MapCore = RedBlackMapCore (*****)
  datatype pmap = M of (pmap, pmap) MapCore.map
  fun cmp (M a, M b) = MapCore.collate cmp cmp (a, b)
  structure Key = struct type ord_key = pmap val compare = cmp end
  structure PMap = RedBlackMapRecFn(Key) (*****)
end
