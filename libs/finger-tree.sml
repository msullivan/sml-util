(* XXX: This only works in SML/NJ because it uses Unsafe.cast in order
 * to do polymorphic recursion... *)

(* Also I think that the asymptotics are wrong if it is actually used
 * persistently, since it doesn't do anything lazily. *)

structure FingerTree =
struct
  type annot = unit
  val a_ident = ()

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
      fun p_add (f : 'a -> 'a finger_tree -> 'a finger_tree) :
          ('b -> 'b finger_tree -> 'b finger_tree) = Unsafe.cast f
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

  fun deep a b c = Deep (a_ident, a, b, c)
  fun node3 a b c = Node3 (a_ident, a, b, c)

  fun fcons a Empty = Single a
    | fcons a (Single b) = deep [a] Empty [b]
    | fcons a (Deep (_, [b, c, d, e], m, sf)) =
      deep [a, b] (p_add fcons (node3 c d e) m) sf
    | fcons a (Deep (_, pr, m, sf)) =
      deep (a :: pr) m sf
  fun fcons' (x, t) = fcons x t

  fun rcons a Empty = Single a
    | rcons a (Single b) = deep [b] Empty [a]
    | rcons a (Deep (_, pr, m, [e, d, c, b])) =
      deep pr (p_add rcons (node3 e d c) m) [b, a]
    | rcons a (Deep (_, pr, m, sf)) =
      deep pr m (sf @ [a])
  fun rcons' (x, t) = rcons x t

  (* STUFF *)
  infixr 5 <<
  fun x << t = fcons x t
  infix 5 >>
  fun t >> x = rcons x t

  end
end
