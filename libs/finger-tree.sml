(* XXX: This only works in SML/NJ because it uses Unsafe.cast in order
 * to do polymorphic recursion... *)

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
  type 'a digit = 'a list

  datatype 'a finger_tree =
           Empty
         | Single of 'a
         | Deep of (annot Lazy.susp * 'a digit * ('a node) finger_tree Lazy.susp * 'a digit)

  datatype 'a view = NilV
                   | ConsV of 'a * 'a finger_tree Lazy.susp
  datatype 'a viewe = NilEV
                    | ConsEV of 'a * 'a finger_tree

  local
      open Lazy

      (* SML doesn't *have* polymorphic recursion, so we fake it by
       * doing an Unsafe.cast before recursing. To try to still
       * provide some semblance of type checking, we give a type
       * annotated version for each variety of function we do this for.
       *)
      fun p_fold (f : ('a * 'b -> 'b) -> 'b -> 'a finger_tree -> 'b) :
          (('c * 'b -> 'b) -> 'b -> 'c finger_tree -> 'b) = Unsafe.cast f
      fun p_add (f : ('a -> T.annot) -> 'a -> 'a finger_tree -> 'a finger_tree) :
          (('b -> T.annot) -> 'b -> 'b finger_tree -> 'b finger_tree) = Unsafe.cast f
      fun p_view (f : ('a -> T.annot) -> 'a finger_tree -> 'a view) :
          (('b -> T.annot) -> 'b finger_tree -> 'b view) = Unsafe.cast f
      fun p_app (f : (('a -> T.annot) -> 'a finger_tree -> 'a list -> 'a finger_tree ->
                      'a finger_tree)) :
          (('b -> T.annot) -> 'b finger_tree -> 'b list -> 'b finger_tree ->
           'b finger_tree) = Unsafe.cast f

      type 'a split_ty = ('a -> T.annot) -> (T.annot -> bool) -> T.annot -> 'a finger_tree
                         -> 'a finger_tree * 'a * 'a finger_tree
      fun p_split (f : 'a split_ty) : 'b split_ty = Unsafe.cast f


  in

  (*** Folds ***)
  fun foldr_node f z (Node2 (_, a, b)) = f (a, f (b, z))
    | foldr_node f z (Node3 (_, a, b, c)) = f (a, f (b, f (c, z)))
  fun foldl_node f z (Node2 (_, a, b)) = f (b, f (a, z))
    | foldl_node f z (Node3 (_, a, b, c)) = f (c, f (b, f (a, z)))

  fun foldr_ftree f z t =
    (case t of
         Empty => z
       | Single x => f (x, z)
       | Deep (_, pr, m, sf) =>
         let fun f' (a, b) = foldr f b a
             fun f'' (a, b) = p_fold foldr_ftree (fn (c, d) => foldr_node f d c) b a
         in f' (pr, f'' (force m, f' (sf, z))) end
    )
  fun foldl_ftree f z t =
    (case t of
         Empty => z
       | Single x => f (x, z)
       | Deep (_, pr, m, sf) =>
         let fun f' (a, b) = foldl f b a
             fun f'' (a, b) = p_fold foldl_ftree (fn (c, d) => foldl_node f d c) b a
         in f' (sf, f'' (force m, f' (pr, z))) end
    )

  fun toList_f t_foldr x = t_foldr (op ::) [] x
  fun toList_node t = toList_f foldr_node t
  fun toList t = toList_f foldr_ftree t

  (*** Measurement lifting ***)
  fun measure_node (Node2 (x, _, _)) = x
    | measure_node (Node3 (x, _, _, _)) = x
  fun measure_digit f l = foldl (fn (x, b) => T.a_plus (f x, b)) T.a_ident l
  fun measure_tree f Empty = T.a_ident
    | measure_tree f (Single x) = f x
    | measure_tree _ (Deep (m, _, _, _)) = force m

  (*** Smart constructors that handle annots *)
  fun deep f a b c =
    let val m = delay (fn _ => T.a_plus (measure_digit f a,
                                         T.a_plus (measure_tree measure_node (force b),
                                                   measure_digit f c)))
    in Deep (m, a, b, c) end
  fun node2 f a b = Node2 (T.a_plus (f a, f b),
                           a, b)
  fun node3 f a b c = Node3 (T.a_plus (f a, T.a_plus (f b, f c)),
                             a, b, c)

  (*** Constructing via cons ***)
  fun fcons_m f a Empty = Single a
    | fcons_m f a (Single b) = deep f [a] (eager Empty) [b]
    | fcons_m f a (Deep (_, [b, c, d, e], m, sf)) =
      (* N.B: eager allegedly fine here according to paper *)
      deep f [a, b] (eager (p_add fcons_m measure_node (node3 f c d e) (force m))) sf
    | fcons_m f a (Deep (_, pr, m, sf)) =
      deep f (a :: pr) m sf

  fun fcons x t = fcons_m T.measure x t
  fun fcons' (x, t) = fcons x t

  fun rcons_m f a Empty = Single a
    | rcons_m f a (Single b) = deep f [b] (eager Empty) [a]
    | rcons_m f a (Deep (_, pr, m, [e, d, c, b])) =
      (* N.B: eager allegedly fine here according to paper *)
      deep f pr (eager (p_add rcons_m measure_node (node3 f e d c) (force m))) [b, a]
    | rcons_m f a (Deep (_, pr, m, sf)) =
      deep f pr m (sf @ [a])
  fun rcons x t = rcons_m T.measure x t
  fun rcons' (x, t) = rcons x t

  fun rcons_f_m t_foldl f t l = t_foldl (fn (x, t) => rcons_m f x t) t l
  fun fcons_f_m t_foldr f t l = t_foldr (fn (x, t) => fcons_m f x t) t l

  fun toTree_f_m t_foldl f x = rcons_f_m t_foldl f Empty x
  fun fromList t = toTree_f_m foldl T.measure t

  (*******************)
  (*** Views on finger trees ***)

  fun viewl_m _ (Empty : 'a finger_tree) = NilV
    | viewl_m _ (Single x) = ConsV (x, eager Empty)
    | viewl_m f (Deep (_, x::xs, m, sf)) = ConsV (x, delay (fn _=>deep_l f xs m sf))
    | viewl_m _ _ = raise Fail "finger invariant violated"
  and deep_l f [] m sf =
      (case p_view viewl_m measure_node (force m) of
           NilV => toTree_f_m foldl f sf
         | ConsV (a, m') => deep f (toList_node a) m' sf)
    | deep_l f pr m sf = deep f pr m sf

  fun viewl t = viewl_m T.measure t

  fun listEnd ls = let val (x::xs) = rev ls in (x, rev xs) end (* EW *)

  fun viewr_m _ (Empty : 'a finger_tree) = NilV
    | viewr_m _ (Single x) = ConsV (x, eager Empty)
    | viewr_m f (Deep (_, pr, m, sf)) =
      let val (x, xs) = listEnd sf
      in ConsV (x, delay (fn _=>deep_r f pr m xs)) end
  and deep_r f pr m [] =
      (case p_view viewr_m measure_node (force m) of
           NilV => toTree_f_m foldl f pr
         | ConsV (a, m') => deep f pr m' (toList_node a))
    | deep_r f pr m sf = deep f pr m sf

  fun viewr t = viewr_m T.measure t

  fun eager_view v = case v of NilV => NilEV
                             | ConsV (x, xs) => ConsEV (x, force xs)
  fun viewel v = eager_view (viewl v)
  fun viewer v = eager_view (viewr v)

  (*** Concatenation ***)
  fun nodes f [a, b] = [node2 f a b]
    | nodes f [a, b, c] = [node3 f a b c]
    | nodes f [a, b, c, d] = [node2 f a b, node2 f c d]
    | nodes f (a::b::c::xs) = node3 f a b c :: nodes f xs
    | nodes _ _ = raise Fail "invariants violated"

  fun app3 f Empty ts xs = fcons_f_m foldr f xs ts
    | app3 f xs ts Empty = rcons_f_m foldl f xs ts
    | app3 f (Single x) ts xs = fcons_m f x (app3 f Empty ts xs)
    | app3 f xs ts (Single x) = rcons_m f x (app3 f xs ts Empty)
    | app3 f (Deep (_, pr1, m1, sf1)) ts (Deep (_, pr2, m2, sf2)) =
      deep f pr1
           (delay
                (fn _=> p_app app3 measure_node (force m1) (nodes f (sf1 @ ts @ pr2)) (force m2)))
           sf2

  fun append xs ys = app3 T.measure xs [] ys

  (*** Splitting ***)
  fun splitDigit f p i [x] = ([], x, [])
    | splitDigit f p i (x::xs) =
      let val i' = T.a_plus (i, f x)
      in
          if p i' then ([], x, xs) else
          let val (l, y, r) = splitDigit f p i' xs
          in (x::l, y, r) end
      end
    | splitDigit _ _ _ _ = raise Fail "empty"

  (* XXX: PROBABLY SHOULD MAKE LAZY *)
  fun splitTree_m f p i (Single x) = (Empty, x, Empty)
    | splitTree_m f p i (Deep (_, pr, m, sf)) =
    let val vpr = T.a_plus (i, measure_digit f pr)
    in if p vpr then let
           val (l, x, r) = splitDigit f p i pr
       in (toTree_f_m foldl f l, x, deep_l f r m sf) end
       else let val vm = T.a_plus (vpr, measure_tree measure_node (force m))
            in if p vm then let
                   val (ml, xs, mr) = p_split splitTree_m measure_node p vpr (force m)
                   val (l, x, r) = splitDigit f p (T.a_plus (vpr, measure_tree measure_node ml))
                                              (toList_node xs)
               in (deep_r f pr (eager ml) l, x, deep_l f r (eager mr) sf) end
               else let val (l, x, r) = splitDigit f p vm sf
                    in (deep_r f pr m l, x, toTree_f_m foldl f r) end
            end
    end
    | splitTree_m _ _ _ Empty = raise Fail "empty"

  fun splitTree p i t = splitTree_m T.measure p i t
  fun split p Empty = (Empty, Empty)
    | split p t =
      if p (measure_tree T.measure t) then
          let val (l, x, r) = splitTree p T.a_ident t
          in (l, fcons x r) end
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
