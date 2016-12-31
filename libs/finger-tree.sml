(* XXX: This only works in SML/NJ because it uses Unsafe.cast in order
 * to do polymorphic recursion... *)

(* Also I think that the asymptotics are wrong if it is actually used
 * persistently, since it doesn't do anything lazily. *)

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
         | Deep of (annot * 'a digit * ('a node) finger_tree * 'a digit)

  local
      (* SML doesn't *have* polymorphic recursion, so we fake it by
       * doing an Unsafe.cast before recursing. To try to still
       * provide some semblance of type checking, we give a type
       * annotated version for each variety of function we do this for.
       *)
      fun p_fold (f : ('a * 'b -> 'b) -> 'b -> 'a finger_tree -> 'b) :
          (('c * 'b -> 'b) -> 'b -> 'c finger_tree -> 'b) = Unsafe.cast f
      fun p_add (f : ('a -> T.annot) -> 'a -> 'a finger_tree -> 'a finger_tree) :
          (('b -> T.annot) -> 'b -> 'b finger_tree -> 'b finger_tree) = Unsafe.cast f
  in

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
         in f' (pr, f'' (m, f' (sf, z))) end
    )
  fun foldl_ftree f z t =
    (case t of
         Empty => z
       | Single x => f (x, z)
       | Deep (_, pr, m, sf) =>
         let fun f' (a, b) = foldl f b a
             fun f'' (a, b) = p_fold foldl_ftree (fn (c, d) => foldl_node f d c) b a
         in f' (sf, f'' (m, f' (pr, z))) end
    )

  fun measure_node (Node2 (x, _, _)) = x
    | measure_node (Node3 (x, _, _, _)) = x
  fun measure_finger f l = foldl (fn (x, b) => T.a_plus (f x, b)) T.a_ident l
  fun measure_tree f Empty = T.a_ident
    | measure_tree f (Single x) = f x
    | measure_tree _ (Deep (m, _, _, _)) = m

  fun deep f a b c = Deep (T.a_plus (measure_finger f a,
                                     T.a_plus (measure_tree measure_node b,
                                               measure_finger f c)),
                           a, b, c)
  fun node2 f a b = Node2 (T.a_plus (f a, f b),
                           a, b)
  fun node3 f a b c = Node3 (T.a_plus (f a, T.a_plus (f b, f c)),
                             a, b, c)

  fun fcons_m f a Empty = Single a
    | fcons_m f a (Single b) = deep f [a] Empty [b]
    | fcons_m f a (Deep (_, [b, c, d, e], m, sf)) =
      deep f [a, b] (p_add fcons_m measure_node (node3 f c d e) m) sf
    | fcons_m f a (Deep (_, pr, m, sf)) =
      deep f (a :: pr) m sf

  fun fcons x t = fcons_m T.measure x t
  fun fcons' (x, t) = fcons x t

  fun rcons_m f a Empty = Single a
    | rcons_m f a (Single b) = deep f [b] Empty [a]
    | rcons_m f a (Deep (_, pr, m, [e, d, c, b])) =
      deep f pr (p_add rcons_m measure_node (node3 f e d c) m) [b, a]
    | rcons_m f a (Deep (_, pr, m, sf)) =
      deep f pr m (sf @ [a])
  fun rcons x t = rcons_m T.measure x t
  fun rcons' (x, t) = rcons x t

  (* TODO: views?? *)

  (* STUFF *)
  infixr 5 <<
  fun x << t = fcons x t
  infix 5 >>
  fun t >> x = rcons x t

  end
end

structure SimpleFingerTree = FingerTreeFn(TrivialMM)
structure SizedFingerTree = FingerTreeFn(SizeMM)
