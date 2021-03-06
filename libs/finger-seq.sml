(* SML implementation of "Finger Trees: A Simple General-purpose Data Structure"
 * by Ralf Hinze and Ross Paterson.
 * http://www.staff.city.ac.uk/~ross/papers/FingerTree.html
 *
 * Finger Trees are a ludicrously handy functional data structure
 * that supports access to the ends in amortized constant time and
 * concatenation and splitting in log time. Thanks to some laziness
 * shenanigans, the amortized constant time bounds hold even when
 * using the tree in a persistent way.
 *
 * This is still in-development testing code.
 *)

(* To use the infix operations from IdxSeq, do:
 * infixr 5 << >< infix 5 >> open IdxSeq.Infix
 *)

(* The original paper on finger trees makes heavy use of polymorphic
 * recursion, which is unfortunately not supported in SML. In my
 * initial version of this code I used Unsafe.cast to fake polymorphic
 * recursion in SML/NJ. This is fun but doesn't work elsewhere.
 *
 * This version ditches polymorphic recursion and instead tags each
 * element in the finger tree with whether it is a terminal object or
 * a node. This means that the type system enforces fewer of our
 * invariants and we have to inject/protect out of our "elem" type that
 * tracks this.
 *
 * There are some advantages of this in our setting too, though.
 * In the original Haskell version, ~everything wound up
 * parameterized over "(Measured a v) => " and Node was a
 * Measured, which made getting the measure of something easy.
 * Since we don't have typeclasses, we had to do the dictionary
 * passing explicitly, which was kind of a pain. Functions with "_m"
 * in their names used to take measure functions as a parameter
 * (and I should clean up the naming).
 * Having everything tagged means we can decide whether to use the
 * object measurement or the node measurement by inspecting the tag.
 *)



(* Should I split this into MEASURABLE and MONOID? Probably not. *)
signature FINGER_TREE =
sig
    type 'a finger_tree
    type annot = int

    datatype 'a viewl = ConsLV of 'a * 'a finger_tree Susp.susp | NilLV
    datatype 'a view = ConsV of 'a * 'a finger_tree | NilV

    val measure : 'a finger_tree -> annot

    val toList : 'a finger_tree -> 'a list
    val fromList : 'a list -> 'a finger_tree

    val foldl : ('a * 'b -> 'b) -> 'b -> 'a finger_tree -> 'b
    val foldr : ('a * 'b -> 'b) -> 'b -> 'a finger_tree -> 'b

    val empty : 'a finger_tree
    val singleton : 'a -> 'a finger_tree
    val fcons : 'a -> 'a finger_tree -> 'a finger_tree
    val fcons' : 'a * 'a finger_tree -> 'a finger_tree
    val rcons : 'a -> 'a finger_tree -> 'a finger_tree
    val rcons' : 'a * 'a finger_tree -> 'a finger_tree

    structure Infix : sig
        val << : 'a * 'a finger_tree -> 'a finger_tree
        val >< : 'a finger_tree * 'a finger_tree -> 'a finger_tree
        val >> : 'a finger_tree * 'a -> 'a finger_tree
    end

    val append : 'a finger_tree -> 'a finger_tree -> 'a finger_tree

    val viewl : 'a finger_tree -> 'a view
    val viewr : 'a finger_tree -> 'a view
    val viewll : 'a finger_tree -> 'a viewl
    val viewlr : 'a finger_tree -> 'a viewl

    exception NotFound
                  (*
    val splitPredLazy3 : (annot -> bool) -> 'a finger_tree
                         -> 'a finger_tree Susp.susp * 'a *
                            'a finger_tree Susp.susp
    val splitPred3 : (annot -> bool) -> 'a finger_tree
                     -> 'a finger_tree * 'a * 'a finger_tree
    val splitPredLazy : (annot -> bool) -> 'a finger_tree
                        -> 'a finger_tree Susp.susp * 'a finger_tree Susp.susp
    val splitPred : (annot -> bool) -> 'a finger_tree
                    -> 'a finger_tree * 'a finger_tree
                  *)

    val forceAll : 'a finger_tree -> 'a finger_tree
end

signature IDX_SEQ =
sig
    type 'a seq
    include FINGER_TREE where type 'a finger_tree = 'a seq

    val split : int -> 'a seq -> 'a seq * 'a seq
    val take : int -> 'a seq -> 'a seq
    val drop : int -> 'a seq -> 'a seq
    val length : 'a seq -> int
    val nth : int -> 'a seq -> 'a
    val deleteAt : int -> 'a seq -> 'a seq
    val spliceAt : 'a seq -> int -> 'a seq -> 'a seq
    val insertAt : 'a -> int -> 'a seq -> 'a seq
    val update : 'a -> int -> 'a seq -> 'a seq
    val subseq : int -> int -> 'a seq -> 'a seq
end

structure IdxSeq : IDX_SEQ =
struct
  (* lurr *)
  type annot = int

  datatype 'a node = Node2 of (annot * 'a * 'a) | Node3 of (annot * 'a * 'a * 'a)
  datatype 'a elem = O of 'a
                   | N of 'a elem node
  (* Things could be made more efficient by having a datatype with
   * the 1-4 digit options but that sounds a lot less pleasant. *)
  type 'a digit = 'a list

  datatype 'a finger_tree =
           Empty
         | Single of 'a elem
         | Deep of (annot Susp.susp *
                    'a elem digit * 'a (*node*) finger_tree Susp.susp * 'a elem digit)

  datatype 'a viewi = NilIV
                    | ConsIV of 'a elem * 'a finger_tree Susp.susp
  datatype 'a viewl = ConsLV of 'a * 'a finger_tree Susp.susp | NilLV
  datatype 'a view = ConsV of 'a * 'a finger_tree | NilV

  local
      open Susp
      fun unO (O x) = x
        | unO _ = raise Fail "fingertree invariants broken"
      fun unN (N x) = x
        | unN _ = raise Fail "fingertree invariants broken"
  in

  (*** Folds ***)

  (* PERF: this implementation follows the original closely
   * and does recursive folds with functions that fold over nodes.
   * It would probably be faster (though less elegant?) to just
   * explicitly do left and right folds over nodes. *)
  fun foldr_node f z (Node2 (_, a, b)) = f (a, f (b, z))
    | foldr_node f z (Node3 (_, a, b, c)) = f (a, f (b, f (c, z)))
  fun foldl_node f z (Node2 (_, a, b)) = f (b, f (a, z))
    | foldl_node f z (Node3 (_, a, b, c)) = f (c, f (b, f (a, z)))

  fun foldr_ftree' f z t =
    (case t of
         Empty => z
       | Single x => f (x, z)
       | Deep (_, pr, m, sf) =>
         let fun f' (a, b) = foldr f b a
             fun f'' (a, b) = foldr_ftree' (fn (c, d) => foldr_node f d (unN c)) b a
         in f' (pr, f'' (force m, f' (sf, z))) end
    )
  fun foldr_ftree f z t = foldr_ftree' (fn (a, b) => f (unO a, b)) z t

  fun foldl_ftree' f z t =
    (case t of
         Empty => z
       | Single x => f (x, z)
       | Deep (_, pr, m, sf) =>
         let fun f' (a, b) = foldl f b a
             fun f'' (a, b) = foldl_ftree' (fn (c, d) => foldl_node f d (unN c)) b a
         in f' (sf, f'' (force m, f' (pr, z))) end
    )
  fun foldl_ftree f z t = foldl_ftree' (fn (a, b) => f (unO a, b)) z t

  fun toList_f t_foldr x = t_foldr (op ::) [] x
  fun toList_node t = toList_f foldr_node t
  fun toList t = toList_f foldr_ftree t

  (*** Measurement lifting ***)
  fun measure_node (Node2 (x, _, _)) = x
    | measure_node (Node3 (x, _, _, _)) = x

  fun measure (O _) = 1
    | measure (N x) = measure_node x

  fun measure_digit l = foldl (fn (x, b) => measure x + b) 0 l
  fun measure_tree Empty = 0
    | measure_tree (Single x) = measure x
    | measure_tree (Deep (m, _, _, _)) = force m


  (*** Smart constructors that handle annots *)
  fun deep a b c =
    let val m = delay (fn _ => measure_digit a + measure_tree (force b) + measure_digit c)
    in Deep (m, a, b, c) end
  fun node2 a b = N (Node2 (measure a + measure b,
                            a, b))
  fun node3 a b c = N (Node3 (measure a + measure b + measure c,
                              a, b, c))

  (*** Constructing via cons ***)
  val empty = Empty
  fun singleton x = Single (O x)

  fun fcons_m a Empty = Single a
    | fcons_m a (Single b) = deep [a] (eager empty) [b]
    | fcons_m a (Deep (_, [b, c, d, e], m, sf)) =
      (* N.B: eager allegedly fine here according to paper *)
      deep [a, b] (eager (fcons_m (node3 c d e) (force m))) sf
    | fcons_m a (Deep (_, pr, m, sf)) =
      deep (a :: pr) m sf

  fun fcons x t = fcons_m (O x) t
  fun fcons' (x, t) = fcons x t

  (* Hacky specialization of list append for our short lists *)
  fun listAdd [a, b, c] d = [a, b, c, d]
    | listAdd [a, b] c = [a, b, c]
    | listAdd [a] b = [a, b]
    | listAdd [] a = [a]
    | listAdd _ _ = raise Fail "lol"


  fun rcons_m a Empty = Single a
    | rcons_m a (Single b) = deep [b] (eager empty) [a]
    | rcons_m a (Deep (_, pr, m, [e, d, c, b])) =
      (* N.B: eager allegedly fine here according to paper *)
      deep pr (eager (rcons_m (node3 e d c) (force m))) [b, a]
    | rcons_m a (Deep (_, pr, m, sf)) =
      deep pr m (listAdd sf a)

  fun rcons x t = rcons_m (O x) t
  fun rcons' (x, t) = rcons x t

  fun rcons_f_m t_foldl t l = t_foldl (fn (x, t) => rcons_m x t) t l
  fun fcons_f_m t_foldr t l = t_foldr (fn (x, t) => fcons_m x t) t l

  fun toTree_f_m t_foldl x = rcons_f_m t_foldl Empty x
  fun fromList t = let fun foldl_O f = foldl (fn (x, z) => f (O x, z))
                   in toTree_f_m foldl_O t end

  (*******************)
  (*** Views on finger trees ***)

  fun viewl_m Empty = NilIV
    | viewl_m (Single x) = ConsIV (x, eager empty)
    | viewl_m (Deep (_, x::xs, m, sf)) = ConsIV (x, delay (fn _=>deep_l xs m sf))
    | viewl_m _ = raise Fail "finger invariant violated"
  and deep_l [] m sf =
      (case viewl_m (force m) of
           NilIV => toTree_f_m foldl sf
         | ConsIV (a, m') => deep (toList_node (unN a)) m' sf)
    | deep_l pr m sf = deep pr m sf

  (* This winds up being a decent optimization *)
  fun listEnd [a, b, c, d] = (d, [a, b, c])
    | listEnd [a, b, c] = (c, [a, b])
    | listEnd [a, b] = (b, [a])
    | listEnd [a] = (a, [])
    | listEnd _ = raise Fail "lol"

  fun viewr_m Empty = NilIV
    | viewr_m (Single x) = ConsIV (x, eager empty)
    | viewr_m (Deep (_, pr, m, sf)) =
      let val (x, xs) = listEnd sf
      in ConsIV (x, delay (fn _=>deep_r pr m xs)) end
  and deep_r pr m [] =
      (case viewr_m (force m) of
           NilIV => toTree_f_m foldl pr
         | ConsIV (a, m') => deep pr m' (toList_node (unN a)))
    | deep_r pr m sf = deep pr m sf

  fun external_view v = case v of NilIV => NilLV
                                | ConsIV (x, xs) => ConsLV (unO x, xs)
  fun viewll t = external_view (viewl_m t)
  fun viewlr t = external_view (viewr_m t)

  fun eager_view v = case v of NilIV => NilV
                             | ConsIV (x, xs) => ConsV (unO x, force xs)
  fun viewl v = eager_view (viewl_m v)
  fun viewr v = eager_view (viewr_m v)

  (*** Concatenation ***)
  fun nodes [a, b] = [node2 a b]
    | nodes [a, b, c] = [node3 a b c]
    | nodes [a, b, c, d] = [node2 a b, node2 c d]
    | nodes (a::b::c::xs) = node3 a b c :: nodes xs
    | nodes _ = raise Fail "invariants violated"

  fun app3 Empty ts xs = fcons_f_m foldr xs ts
    | app3 xs ts Empty = rcons_f_m foldl xs ts
    | app3 (Single x) ts xs = fcons_m x (app3 Empty ts xs)
    | app3 xs ts (Single x) = rcons_m x (app3 xs ts Empty)
    | app3 (Deep (_, pr1, m1, sf1)) ts (Deep (_, pr2, m2, sf2)) =
      deep pr1
           (delay
                (fn _=> app3 (force m1) (nodes (sf1 @ ts @ pr2)) (force m2)))
           sf2

  fun append xs ys = app3 xs [] ys

  (*** Splitting ***)
  fun splitDigit n i [x] = ([], x, [])
    | splitDigit n i (x::xs) =
      let val i' = i + measure x
      in
          if n < i' then ([], x, xs) else
          let val (l, y, r) = splitDigit n i' xs
          in (x::l, y, r) end
      end
    | splitDigit _ _ _ = raise Fail "empty"

  exception NotFound
  (* I think making this lazy is probably good >_> *)
  fun splitTree_m n i (Single x) = (eager empty, x, eager empty)
    | splitTree_m n i (Deep (_, pr, m, sf)) =
    let val vpr = i + measure_digit pr
    in if n < vpr then let
           val (l, x, r) = splitDigit n i pr
       in (delay (fn _=>toTree_f_m foldl l), x,
           delay (fn _=>deep_l r m sf)) end
       else let val vm = vpr + measure_tree (force m)
            in if n < vm then let
                   val (ml, xs, mr) = splitTree_m n vpr (force m)
                   val xs = unN xs
                   val (l, x, r) = splitDigit n (vpr + measure_tree (force ml))
                                              (toList_node xs)
               in (delay (fn _=>deep_r pr ml l), x,
                   delay (fn _=>deep_l r mr sf)) end

               else let val (l, x, r) = splitDigit n vm sf
                    in (delay (fn _=>deep_r pr m l), x,
                        delay (fn _=>toTree_f_m foldl r)) end
            end
    end
    | splitTree_m _ _ Empty = raise NotFound

  fun splitTree_m' n i (Single x) = (empty, x, empty)
    | splitTree_m' n i (Deep (_, pr, m, sf)) =
    let val vpr = i + measure_digit pr
    in if n < vpr then let
           val (l, x, r) = splitDigit n i pr
       in (toTree_f_m foldr l, x, deep_l r m sf) end
       else let val vm = vpr + measure_tree (force m)
            in if n < vm then let
                   val (ml, xs, mr) = splitTree_m' n vpr (force m)
                   val xs = unN xs
                   val (l, x, r) = splitDigit n (vpr + measure_tree ml)
                                              (toList_node xs)
               in (deep_r pr (eager ml) l, x, deep_l r (eager mr) sf) end

               else let val (l, x, r) = splitDigit n vm sf
                    in (deep_r pr m l, x, toTree_f_m foldr r) end
            end
    end
    | splitTree_m' _ _ Empty = raise NotFound


  fun splitLazy3 n t =
    let val (l, x, r) = splitTree_m n 0 t
    in (l, unO x, r) end

  fun split3 n t =
    let val (l, x, r) = splitTree_m' n 0 t
    in (l, unO x, r) end

  fun splitLazy i Empty = (eager empty, eager empty)
    | splitLazy i t =
      if i < measure_tree t then
          let val (l, x, r) = splitLazy3 i t
          in (l, delay (fn _=>fcons x (force r))) end
      else
          (eager t, eager empty)

  fun split i Empty = (Empty, Empty)
    | split i t =
      if i < measure_tree t then
          let val (l, x, r) = split3 i t
          in (l, fcons x r) end
      else
          (t, Empty)

  fun forceAll t = (foldl_ftree (fn _ => ()) () t; t)
  (* It really sketches me out that just forcing
   * the annotation forces the whole tree *)
  fun forceAll (t as Deep (m, _, _, _)) = (force m; t)
    | forceAll t = t
  end

  infixr 5 << >< infix 5 >>
  structure Infix = struct
    fun x << t = fcons x t
    fun xs >< ys = append xs ys
    fun t >> x = rcons x t
  end

  (* This is kind of gross, but I want it named measure_tree instead
   * of measure but I still want to use measure for elems inside... *)
  val measure = measure_tree
  val foldl = foldl_ftree
  val foldr = foldr_ftree


  (*********** The sequence stuff **************)
  open Susp
  type 'a seq = 'a finger_tree

  infixr 5 << >< infix 5 >> open Infix

  val length = measure

  fun take n s =
    let val (l, r) = splitLazy n s
    in force l end
  fun drop n s =
    let val (l, r) = splitLazy n s
    in force r end

  fun subseq from to s = take (to-from) (drop from s)

  (* Many of these could be more efficient... *)
  fun nth i s =
    let val (_, x, _) = splitLazy3 i s
    in x end
    handle _ => raise Subscript

  fun update x i s =
    let val (l, _, r) = split3 i s
    in l >< x << r end
    handle _ => raise Subscript

  fun deleteAt n s =
    let val (l, _, r) = split3 n s
    in l >< r end
    handle _ => raise Subscript
  fun spliceAt s' n s =
    if n < 0 orelse n > length s then raise Subscript else
    let val (l, r) = split n s
    in l >< s' >< r end
  fun insertAt x n s = spliceAt (singleton x) n s
end
