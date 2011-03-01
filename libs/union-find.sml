signature UNION_FIND =
sig
  structure Key : ORD_KEY
  type map

  val empty : map
  val find_rep : map -> Key.ord_key -> Key.ord_key
  val union_reps : map -> Key.ord_key -> Key.ord_key -> map

end

functor UnionFindFn (K : ORD_KEY) : UNION_FIND =
struct
  structure Key = K
  structure M = GoodMapFn(Key)
  
  (* This is a ref so that we can do path compression "behind the scenes" without
   * forcing the user to deal with new versions of the map after lookups.
   * When we actually make changes, we put them into a new ref.
   *)

  type map = Key.ord_key M.map ref

  val empty : map = ref M.empty

  fun eq e1 e2 = Key.compare (e1, e2) = EQUAL

  (* Find the representative of an element, does path compression if necessary,
   * and returns the new map *)
  fun find_rep' m el = 
      (case M.look m el of
         (SOME v) =>
           let val (m', parent) = find_rep' m v
           in (M.bind m' el parent, parent) end
         | NONE => (m, el))

  (* Find the representative element of the set e1 is in.
   * Transparently does path compression. *)
  fun find_rep mr el =
      let val (m', el') = find_rep' (!mr) el
          val () = mr := m'
      in el' end

  (* Union two sets together. The set x is unioned into set y, and
   * the canonical element of set y is the canonical element of the
   * new set.
   *)
  fun union_reps mr x y =
      let val (m', xroot) = find_rep' (!mr)  x
          val (m', yroot) = find_rep' m' y
          val m' = M.bind m' xroot yroot (*bind x to y, so y is x's parent. *)
      in ref m' end
end
