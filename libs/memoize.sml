(* Implementation of an "auto-memoizing" wrapper.
 * Given a hash function and an equality predicate for the domain of
 * a function and a function (sort of; see below), Memoize.memoize 
 * returns a memoized version of that function.
 *
 * This relies on SML/NJ's HashTable structure.
 *
 * Since, unlike in some other languages, we cannot override the bindings
 * visible earlier in the program, if the target function actually calls
 * itself we will have no way to override the recursive calls. Thus the
 * function must instead be written to take the function to invoke
 * recursively as its first argument, which will be provided by the
 * memoization wrapper.
 * This is exactly how functions need to be written to use the fixed
 * point combinator on it!
 * (see http://www.msully.net/~sully/files/fix.sml)
 *)

signature MEMOIZE =
sig
  val memoize : ('a -> word) -> (('a * 'a) -> bool) ->
                (('a -> 'b) -> ('a -> 'b)) -> ('a -> 'b)
end

structure Memoize : MEMOIZE =
struct
  structure HT = HashTable
  fun memoize hash eq f =
      let val table = HT.mkTable (hash, eq) (128, Fail "not found")
          fun wrapper x =
              case HT.find table x of
                  SOME v => v
                | NONE =>
                  let val v = f' x
                      val () = HT.insert table (x, v)
                  in v end
          and f' x = f wrapper x
      in f' end
end

fun fib' _ 0 = 0 : IntInf.int
  | fib' _ 1 = 1
  | fib' f n = (f (n-1)) + (f (n-2))

fun hyperbinary' _ (0 : IntInf.int) = (1 : IntInf.int)
  | hyperbinary' h n = if n mod 2 = 1 then h ((n-1) div 2)
                       else h ((n div 2) - 1) + h (n div 2)

val fib = Memoize.memoize Word.fromInt (op =) fib'
val hyperbinary = Memoize.memoize Word.fromLargeInt (op =) hyperbinary'

val test = hyperbinary 100000000000000
