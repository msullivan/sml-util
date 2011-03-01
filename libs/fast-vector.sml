(* SML/NJ has a very poorly performing implementation of Vectors, since
 * the only primitive operation to build a vector provided by the runtime
 * is "turn this list into a vector", which really kind of sucks.
 * As it turns out, thanks to the magic of abstraction, we can *almost*
 * provide a drop in replacement for vectors by using array as the 
 * implementation of vector but ascribing to VECTOR. This does not quite
 * maintain all the same behavior: SML/NJ has vector literals that will
 * not work, and pretty printing vectors won't work. The actual real
 * change, however, is in the behavior of equality. Vector equality
 * is structural equality while array equality is pointer equality.
 * For most applications, this should be fine... 
 * Since Array has a bunch of functions that operate on vectors, I needed
 * to also provide an Array.
 *
 * Allowing Array to take advantage of the internal representation of
 * vectors while still hiding that vector is array to external code
 * involved some shenanigans. The Vector and Array are both defined
 * inside of another structure Package and then pulled out later.
 * Since Package opaquely ascribes to the sig PACKAGE, the abstract
 * types that are not defined (just Vector.vector) inside it are
 * hidden. However, they are visible inside the structure, so Array
 * can take use of them...
 *
 * TODO: slices
 *)

signature PACKAGE =
sig
  structure Vector : VECTOR
  structure Array : ARRAY where type 'a array = 'a Array.array
                            and type 'a vector = 'a Vector.vector
end

structure Package :> PACKAGE =
struct
  (* Argh I don't want to ascribe transparently. *)
  structure Vector : VECTOR =
  struct
    open Array
    type 'a vector = 'a array

    fun map f v = tabulate (length v, fn i => f (sub (v, i)))
    fun mapi f v = tabulate (length v, fn i => f (i, sub (v, i)))

    (* FIXME! *)
    fun vecToList v = foldr (op ::) nil v
    fun concat v = fromList (List.concat (List.map vecToList v))

    fun update (v, i, x) =
        mapi (fn (i', x') => if i = i' then x else x') v
  end


  structure Array : ARRAY =
  struct
    structure V = Vector
    open Array
    type 'a vector = 'a V.vector

    fun zeroArray () = tabulate (0, fn _ => raise Fail "lol!")

    val copyVec = copy

    fun copyWhole a =
        case length a of
            0 => zeroArray ()
          | n =>
            let val a' = array (n, sub (a, 0))
                val () = copy {src=a, dst=a', di=0}
            in a' end

    val vector = copyWhole
  end
end

structure Vector = Package.Vector
type 'a vector = 'a Vector.vector
structure Array = Package.Array
