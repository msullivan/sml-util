(* A bunch of random utility functions that I didn't feel like putting
 * reasonable places *)

structure Util =
struct
  fun id x = x

  fun curry2 f x y = f (x, y)
  fun curry3 f x y z = f (x, y, z)
  fun curry4 f x y z w = f (x, y, z, w)

  fun uncurry2 f (x, y) = f x y
  fun uncurry3 f (x, y, z) = f x y z
  fun uncurry4 f (x, y, z, w) = f x y z w

  fun first (x, _) = x
  fun second (_, y) = y

  fun first3 (x, _, _) = x
  fun second3 (_, y, _) = y
  fun third3 (_, _, z) = z

  datatype ('a, 'b) Sum = Left of 'a | Right of 'b

  fun vecToList v = Vector.foldr (op ::) nil v
  fun vecToArray v = Array.tabulate (Vector.length v, fn i => Vector.sub (v, i))
  fun arrayToList a = (vecToList o Array.vector) a

  fun upto n = List.tabulate (n, id)
  fun enumerate l = ListPair.zip (upto (length l), l)

  fun optionToList NONE = []
    | optionToList (SOME x) = [x]

  (* Use of this function should probably be avoided. *)
  fun listSet _ [] _ = raise Subscript
    | listSet 0 (_::xs) x = x::xs
    | listSet n (x::xs) y = x :: (listSet (n-1) xs y)

  (* does a map while carrying along an accumulator *)
  fun foldlMap f z l =
      let fun helper (x, (l, z)) =
              let val (x', z') = f (x, z) in (x'::l, z') end
          val (l', z') = foldl helper ([], z) l
      in (rev l', z') end

  fun split f l =
      let fun splitter' cur blocks [] = rev (map rev (cur::blocks))
            | splitter' cur blocks [x] = splitter' (x::cur) blocks []
            | splitter' cur blocks (x1::x2::xs) =
              if f (x1, x2) then
                  splitter' [] ((x1::cur)::blocks) (x2::xs)
              else
                  splitter' (x1::cur) blocks (x2::xs)
      in splitter' [] [] l end

  fun groupBy cmp =
      let fun loop _ nil = nil
            | loop z (x::nil) = [rev (x::z)]
            | loop z (x1::x2::xs) =
              if cmp (x1, x2) then loop (x1::z) (x2::xs)
              else rev (x1::z) :: loop nil (x2::xs)
      in loop [] end

  fun option z _ NONE = z
    | option _ f (SOME x) = f x

  fun rotate_lists nil = nil
    | rotate_lists (nil::l) = nil
    | rotate_lists l =
      let val (xs, rest) = ListPair.unzip (List.mapPartial List.getItem l)
      in xs :: rotate_lists rest end

  fun finally f final =
      f () before ignore (final ())
      handle e => (final (); raise e)

  (* A function to compute all permutations of a list that I wrote to
   * convince myself that I could do it after I was having a lot of
   * trouble understanding Haskell's permutations function... *)
  fun permutations xs = let
      fun perms_with_start x [] = [[x]]
        | perms_with_start x xs = map (fn ys => x :: ys) (permutations xs)
      fun loop [] _ = []
        | loop (x::xs) t = perms_with_start x (rev (List.revAppend (xs, t))) @
                           loop xs (x::t)
  in loop xs [] end

end
