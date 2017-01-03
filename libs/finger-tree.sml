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
 * This is still in-development testing code. Nothing really has the
 * right interface yet.
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

(* TODO: This needs to be made to export a reasonable interface *)

(* Should I split these? *)
signature MEASURABLE_MONOID =
sig
    type 'a t
    type annot (* XXX: polymorphic?? *)
    val measure : 'a t -> annot
    val a_ident : annot
    val a_plus : annot * annot -> annot
end

structure TrivialMM : MEASURABLE_MONOID =
struct
    type 'a t = 'a
    type annot = unit
    val a_ident = ()
    fun measure _ = a_ident
    fun a_plus (_, _) = a_ident
end

structure SizeMM : MEASURABLE_MONOID =
struct
    type 'a t = 'a
    type annot = int
    val a_ident = 0
    fun measure _ = 1
    fun a_plus (x, y) = x+y
end

functor FingerTreeFn(T : MEASURABLE_MONOID) =
struct
  type 'a t = 'a T.t
  type annot = T.annot

  datatype 'a node = Node2 of (annot * 'a * 'a) | Node3 of (annot * 'a * 'a * 'a)
  datatype 'a elem = O of 'a
                   | N of 'a elem node
  type 'a digit = 'a list

  datatype 'a finger_tree =
           Empty
         | Single of 'a elem
         | Deep of (annot Lazy.susp *
                    'a elem digit * 'a (*node*) finger_tree Lazy.susp * 'a elem digit)

  datatype 'a viewi = NilIV
                    | ConsIV of 'a elem * 'a finger_tree Lazy.susp
  datatype 'a view = NilV
                   | ConsV of 'a * 'a finger_tree Lazy.susp
  datatype 'a viewe = NilEV
                    | ConsEV of 'a * 'a finger_tree
  local
      open Lazy
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

  fun measure (O x) = T.measure x
    | measure (N x) = measure_node x

  fun measure_digit l = foldl (fn (x, b) => T.a_plus (measure x, b)) T.a_ident l
  fun measure_tree Empty = T.a_ident
    | measure_tree (Single x) = measure x
    | measure_tree (Deep (m, _, _, _)) = force m


  (*** Smart constructors that handle annots *)
  fun deep a b c =
    let val m = delay (fn _ => T.a_plus (measure_digit a,
                                         T.a_plus (measure_tree (force b),
                                                   measure_digit c)))
    in Deep (m, a, b, c) end
  fun node2 a b = N (Node2 (T.a_plus (measure a, measure b),
                            a, b))
  fun node3 a b c = N (Node3 (T.a_plus (measure a, T.a_plus (measure b, measure c)),
                                a, b, c))

  (*** Constructing via cons ***)
  fun fcons_m a Empty = Single a
    | fcons_m a (Single b) = deep [a] (eager Empty) [b]
    | fcons_m a (Deep (_, [b, c, d, e], m, sf)) =
      (* N.B: eager allegedly fine here according to paper *)
      deep [a, b] (eager (fcons_m (node3 c d e) (force m))) sf
    | fcons_m a (Deep (_, pr, m, sf)) =
      deep (a :: pr) m sf

  fun fcons x t = fcons_m (O x) t
  fun fcons' (x, t) = fcons x t

  fun rcons_m a Empty = Single a
    | rcons_m a (Single b) = deep [b] (eager Empty) [a]
    | rcons_m a (Deep (_, pr, m, [e, d, c, b])) =
      (* N.B: eager allegedly fine here according to paper *)
      deep pr (eager (rcons_m (node3 e d c) (force m))) [b, a]
    | rcons_m a (Deep (_, pr, m, sf)) =
      deep pr m (sf @ [a])

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
    | viewl_m (Single x) = ConsIV (x, eager Empty)
    | viewl_m (Deep (_, x::xs, m, sf)) = ConsIV (x, delay (fn _=>deep_l xs m sf))
    | viewl_m _ = raise Fail "finger invariant violated"
  and deep_l [] m sf =
      (case viewl_m (force m) of
           NilIV => toTree_f_m foldl sf
         | ConsIV (a, m') => deep (toList_node (unN a)) m' sf)
    | deep_l pr m sf = deep pr m sf

  fun listEnd ls = let val rls = rev ls in (hd rls, rev (tl rls)) end (* EW *)

  fun viewr_m Empty = NilIV
    | viewr_m (Single x) = ConsIV (x, eager Empty)
    | viewr_m (Deep (_, pr, m, sf)) =
      let val (x, xs) = listEnd sf
      in ConsIV (x, delay (fn _=>deep_r pr m xs)) end
  and deep_r pr m [] =
      (case viewr_m (force m) of
           NilIV => toTree_f_m foldl pr
         | ConsIV (a, m') => deep pr m' (toList_node (unN a)))
    | deep_r pr m sf = deep pr m sf

  fun external_view v = case v of NilIV => NilV
                                | ConsIV (x, xs) => ConsV (unO x, xs)

  fun viewl t = external_view (viewl_m t)
  fun viewr t = external_view (viewr_m t)

  fun eager_view v = case v of NilV => NilEV
                             | ConsV (x, xs) => ConsEV (x, force xs)
  fun viewel v = eager_view (viewl v)
  fun viewer v = eager_view (viewr v)

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
  fun splitDigit p i [x] = ([], x, [])
    | splitDigit p i (x::xs) =
      let val i' = T.a_plus (i, measure x)
      in
          if p i' then ([], x, xs) else
          let val (l, y, r) = splitDigit p i' xs
          in (x::l, y, r) end
      end
    | splitDigit _ _ _ = raise Fail "empty"

  (* I think making this lazy is probably good >_> *)
  fun splitTree_m p i (Single x) = (eager Empty, x, eager Empty)
    | splitTree_m p i (Deep (_, pr, m, sf)) =
    let val vpr = T.a_plus (i, measure_digit pr)
    in if p vpr then let
           val (l, x, r) = splitDigit p i pr
       in (delay (fn _=>toTree_f_m foldl l), x,
           delay (fn _=>deep_l r m sf)) end
       else let val vm = T.a_plus (vpr, measure_tree (force m))
            in if p vm then let
                   val (ml, xs, mr) = splitTree_m p vpr (force m)
                   val xs = unN xs
                   val (l, x, r) = splitDigit p (T.a_plus (vpr,
                                                             measure_tree (force ml)))
                                              (toList_node xs)
               in (delay (fn _=>deep_r pr ml l), x,
                   delay (fn _=>deep_l r mr sf)) end

               else let val (l, x, r) = splitDigit p vm sf
                    in (delay (fn _=>deep_r pr m l), x,
                        delay (fn _=>toTree_f_m foldl r)) end
            end
    end
    | splitTree_m _ _ Empty = raise Fail "empty"

  fun splitTree p i t =
    let val (l, x, r) = splitTree_m p i t
    in (l, unO x, r) end

  fun split p Empty = (Empty, Empty)
    | split p t =
      if p (measure_tree t) then
          let val (l, x, r) = splitTree p T.a_ident t
          in (force l, fcons x (force r)) end
      else
          (t, Empty)


  (* STUFF *)
  infixr 5 << >< infix 5 >>
  structure Infix = struct
  fun x << t = fcons x t
  fun xs >< ys = append xs ys
  fun t >> x = rcons x t
  end
  open Infix

  fun forceAll t = (foldl_ftree (fn _ => ()) () t; t)
  (* It really sketches me out that just forcing
   * the annotation forces the whole tree *)
  fun forceAll (t as Deep (m, _, _, _)) = (force m; t)
    | forceAll t = t
  end
end

structure SimpleFingerTree = FingerTreeFn(TrivialMM)
structure SizedFingerTree =
struct
  structure F = FingerTreeFn(SizeMM)
  open F

  fun splitAt i t = split (fn i' => i < i') t

end
