(* I felt like toying around with SML/NJ's support for laziness. 
 * To run this, run sml/nj with the -Cparser.lazy-keyword=true flag.
 *)

open Lazy

structure LazyUtil =
struct
  fun force ($x) = x
  fun lift f ($x) = $(f x)
  fun liftHalf f (x, $y) = $(f (x, y))
  fun lazy fix f = f (fix f)
end

structure LazyList =
struct
  local
      open LazyUtil
  in

  infixr 5 >> ++
  datatype lazy 'a lazylist = Nil | >> of 'a * 'a lazylist

  fun hd Nil = raise Empty
    | hd (x>>_) = x
  fun lazy tl Nil = raise Empty
         | tl (_>>xs) = xs

  (* Create a singleton lazylist *)
  fun s x = x >> Nil

  fun take (_, 0) = Nil
    | take (Nil, _) = raise Subscript
    | take ((x>>xs), n) = x>>(take (xs, n-1))

  (* This will get sad on infinite lists *)
  fun foldl f =
      let fun lazy loop z Nil = z
                 | loop z (x>>xs) = loop (f (x, z)) xs
      in loop end
  fun foldlStrict f z = force o foldl (liftHalf f) ($z)
                        
  fun foldr f z =
      let fun lazy loop Nil = z
                 | loop (x>>xs) = f (x, loop xs)
      in loop end
  fun foldrStrict f z = force o foldr (liftHalf f) ($z)

  fun filter p xs = foldr (fn (x, xs) => if p then x >> xs else xs) Nil xs

  fun (xs ++ ys) = foldr (op >>) ys xs

  fun map f xs = foldr (fn (x, xs) => f x >> xs) Nil xs
  fun concatMap f xs = foldr (fn (x, xs) => f x ++ xs) Nil xs

  fun length l = foldlStrict (fn (_, n) => n+1) 0 l
  fun rev l = foldl (op >>) Nil l

  fun app _ Nil = ()
    | app f (x>>xs) = (f x; app f xs)

  (* Some infinite list utilities from Haskell *)
  fun lazy repeat x = x >> (repeat x)
  fun lazy cycle l = l ++ (cycle l)
  fun lazy iterate f x = x >> iterate f (f x)

  fun lazy zip (Nil, _) = Nil
         | zip (_, Nil) = Nil
         | zip (x>>xs, y>>ys) = (x, y)>>zip (xs, ys)

  fun lazy zipWith f xs ys = map f (zip (xs, ys))

  fun groupBy cmp =
      let fun lazy loop _ Nil = Nil
                 | loop z (x>>Nil) = rev (x>>z) >> Nil
                 | loop z (x1>>x2>>xs) = 
                   if cmp (x1, x2) then loop (x1>>z) (x2>>xs)
                   else rev (x1>>z) >> loop Nil (x2>>xs)
      in loop Nil end

  (* For getting in and out of lazy land... *)
  fun fromList l = List.foldr (op >>) Nil l
  fun toList l = foldrStrict (op::) nil l
  fun ltake arg = (toList o take) arg
  val fL = fromList
  val tL = toList
  fun t n l = ltake (l, n)

  fun show p l =
      let val c = fromList o explode
          fun lazy loop Nil = c "]"
                 | loop (x>>Nil) = c (p x ^ "]")
                 | loop (x>>xs) = c (p x ^ ", ") ++ loop xs
      in #"[" >> loop l end
  end

  fun sshow l = #"\"">>concatMap (fL o explode o Char.toCString) l ++ (s #"\"")
end

infixr 5 >> ++
open LazyList
open LazyUtil

val nats = iterate (fn n => n+1) 0
val positives = tl nats

val i0 : IntInf.int = 0
val i1 : IntInf.int = 1
(* And now, the moment we've all been waiting for... *)
val rec lazy fibs = 0 >> 1 >> zipWith (op +) fibs (tl fibs)
val rec lazy ifibs = i0 >> i1 >> zipWith (op +) ifibs (tl ifibs)

val fs = fL o explode
val s = fs "hello, world\n"

val ishow = show Int.toString
val iishow = show IntInf.toString
val printchar = print o str
fun lprint f l = app printchar (show f l)
val lprint' = app printchar
val iprint = lprint Int.toString
val iiprint = lprint IntInf.toString

fun eq x y = x = y
fun const k _ = k

(* map length . groupBy (const(=='\\')) .  fix $ show *)
val pow2s = (map length o groupBy (fn (_,x) => x = #"\\") o fix) sshow
