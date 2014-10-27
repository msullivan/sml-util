(* We *can* do the ST monad in SML, using functors to get the
 * necessary rank-2 type. Unfortunately it doesn't fit into the
 * monad.sml framework, though, *)

infixr 0 $ infix 1 >>= >> infixr 1 =<< >=> <=< infix 4 <$> <*> fun f $ x = f x

(* Signature definitions for an ST monad *)
signature ST_MONAD =
sig
  type ('s, 'a) st

  val return : 'a -> ('s, 'a) st
  val >>= : ('s, 'a) st * ('a -> ('s, 'b) st) -> ('s, 'b) st

  type ('a, 's) st_ref
  val newSTRef : 'a -> ('s, ('s, 'a) st_ref) st
  val readSTRef : ('s, 'a) st_ref -> ('s, 'a) st
  val writeSTRef : ('s, 'a) st_ref -> 'a -> ('s, unit) st
end

signature INITIAL_ST_MONAD =
sig
  include ST_MONAD
  val unsafeRunST : ('s, 'a) st -> 'a
end

structure STMonad :> INITIAL_ST_MONAD =
struct
  type ('s, 'a) st = unit -> 'a
  fun unsafeRunST m = m ()

  fun return x () = x
  fun m >>= k = fn () => (k (m ())) ()

  type ('s, 'a) st_ref = 'a ref

  fun newSTRef x () = ref x
  fun readSTRef r () = !r
  fun writeSTRef r v () = r := v
end

signature ST_ACTION =
sig
  type t
  val getAction : unit -> ('s, t) STMonad.st
end

signature RUN_ST =
sig
  type t
  val runST : unit -> t
end

functor RunST(A : ST_ACTION) : RUN_ST =
struct
  type t = A.t
  fun runST () = STMonad.unsafeRunST (A.getAction ())
end

(* And seal it off! *)
structure STMonad :> ST_MONAD where type ('s, 'a) st = ('s, 'a) STMonad.st = STMonad


(* We could also implement this *without* using refs by doing a state
 * monad style thing with a map from keys to values. An st_ref would be
 * a key into the table and a universal type tag.
 * (Or use unsafeCast. Whatever.) *)

(*****************************************************************)
open STMonad

fun fetchIncrement r =
    readSTRef r >>= (fn x =>
    writeSTRef r (x+1) >>= (fn () =>
    return x))


structure Test1 : ST_ACTION =
struct
  type t = int
  fun getAction () =
      newSTRef 2 >>= (fn r =>
      fetchIncrement r >>= (fn i =>
      fetchIncrement r >>= (fn i' =>
      return (i+i'))))
end

(* This can't work: *)
(*
structure BrokenTest : ST_ACTION =
struct
  type t = (int, int) st_ref
  fun getAction () = newSTRef 2
end
*)
