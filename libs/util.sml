(* A bunch of random utility functions that I didn't feel like putting
 * reasonable places *)

structure Util =
struct
  infixr 0 $
  fun f $ x = f x

  fun id x = x
  fun flip f x y = f y x
  fun const x _ = x
  fun thunk f x () = f x

  fun curry2 f x y = f (x, y)
  fun curry3 f x y z = f (x, y, z)
  fun curry4 f x y z w = f (x, y, z, w)

  fun uncurry2 f (x, y) = f x y
  fun uncurry3 f (x, y, z) = f x y z
  fun uncurry4 f (x, y, z, w) = f x y z w

  fun first (x, _) = x
  fun second (_, y) = y

  fun replicate 0 _ = []
    | replicate n x = x :: (replicate (n - 1) x)

  fun first3 (x, _, _) = x
  fun second3 (_, y, _) = y
  fun third3 (_, _, z) = z

  datatype ('a, 'b) Sum = Left of 'a | Right of 'b

  fun vecToList v = Vector.foldr (op ::) nil v
  fun vecToArray v = Array.tabulate (Vector.length v, fn i => Vector.sub (v, i))
  fun arrayToList a = (vecToList o Array.vector) a
  fun copyArray v = Array.tabulate (Array.length v, fn i => Array.sub (v, i))

  fun upto n = List.tabulate (n, id)
  fun enumerate l = ListPair.zip (upto (length l), l)

  fun optionToList NONE = []
    | optionToList (SOME x) = [x]

  fun even x = x mod 2 = 0
  val odd = not o even

  fun minBy f x y = case Int.compare (f x, f y) of GREATER => y | _ => x

  fun mapBoth f (x,y) = (f x, f y)
  fun apBoth (f,g) (x,y) = (f x, g y)

  (* TODO: make this tail-recursive *)
  fun intersperse _ [] = []
    | intersperse _ [x] = [x]
    | intersperse x (y::ys) = y :: x :: intersperse x ys

  fun intercalate (xs : 'a list) (xss : 'a list list) =
      List.concat (intersperse xs xss)

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

  fun foldl1 f (x::xs) = foldl f x xs
    | foldl1 _ _ = raise Fail "foldl1: empty list"
  fun foldr1 _ [x] = x
    | foldr1 f (x::xs) = f (x, foldr1 f xs)
    | foldr1 _ _ = raise Fail "foldr1: empty list"

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

  fun dedup (x::l) = foldl (fn (e,a) => e :: (List.filter (fn x => not (x = e)) a)) [x] l

  fun option z _ NONE = z
    | option _ f (SOME x) = f x

  fun rotate_lists nil = nil
    | rotate_lists (nil::l) = nil
    | rotate_lists l =
      let val (xs, rest) = ListPair.unzip (List.mapPartial List.getItem l)
      in xs :: rotate_lists rest end

  fun finally f final =
      f () before (final ())
      handle e => (final (); raise e)

  fun after f g x =
      finally (fn () => f x) (fn () => g x)

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

  fun containsBy f x l = List.exists (fn y => f (x, y)) l
  fun contains x l = containsBy (op =) x l

  fun sequenceLengths f l =
      let fun loop [] _ = []
            | loop (x::xs) n =
              if f x then (n+1) :: loop xs (n+1)
              else 0 :: loop xs 0
      in rev (loop (rev l) 0) end

  fun max_elem _ nil = NONE
    | max_elem cmp l =
      SOME (
      foldl1 (fn ((i, x), (i', x')) =>
                 if cmp (x, x') = GREATER then (i, x) else (i', x'))
             (enumerate l))
  
end
