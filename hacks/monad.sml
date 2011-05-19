(* Inspired by
 * http://existentialtype.wordpress.com/2011/05/01/of-course-ml-has-monads/ *)
(* TODO: maybe have a hierarchy of signatures: Functor, Applicative, Monad *)

(* Infix operators can be nice. *)
infixr 0 $
infix 1 >>= >>
infixr 1 =<< >=> <=<
infix 4 <$> <*>

(* Useful utility functions *)
fun f $ x = f x
fun id x = x

signature MONAD =
sig
  type 'a m
  val return : 'a -> 'a m
  val >>= : 'a m * ('a -> 'b m) -> 'b m
end

signature MONAD_UTIL =
sig
  include MONAD

  (* A synonym for >>= *)
  val bind : 'a m -> ('a -> 'b m) -> 'b m

  (* A handful of sequencing related operators. *)
  val =<< : ('a -> 'b m) * 'a m -> 'b m
  val >> : 'a m * 'b m -> 'b m
  val >=> : ('a -> 'b m) * ('b -> 'c m) -> 'a -> 'c m
  val <=< : ('a -> 'b m) * ('c -> 'a m) -> 'c -> 'b m

  (* Functions for sequencing lists. *)
  val sequence : 'a m list -> 'a list m
  val sequence_ : 'a m list -> unit m
  val mapM : ('a -> 'b m) -> 'a list -> 'b list m
  val mapM_ : ('a -> 'b m) -> 'a list -> unit m
  val forM : 'a list -> ('a -> 'b m) -> 'b list m
  val forM_ : 'a list -> ('a -> 'b m) -> unit m

  (* Functions for lifting other functions into monads. *)
  val liftM : ('a -> 'b) -> 'a m -> 'b m
  val liftM2 : ('a -> 'b -> 'c) -> 'a m -> 'b m -> 'c m
  val liftM3 : ('a -> 'b -> 'c -> 'd) -> 'a m -> 'b m -> 'c m -> 'd m
  val liftM2' : ('a * 'b -> 'c) -> 'a m * 'b m -> 'c m

  (* Things that properly belong in a functor or applicative. *)
  val fmap : ('a -> 'b) -> 'a m -> 'b m
  val <$> : ('a -> 'b) * 'a m -> 'b m
  val ap : ('a -> 'b) m -> 'a m -> 'b m
  val <*> : ('a -> 'b) m * 'a m -> 'b m

  val forever : 'a m -> 'b m
  val join : 'a m m -> 'a m
end

functor MonadUtil(M : MONAD) : MONAD_UTIL =
struct
  open M

  fun bind m f = m >>= f
  fun f =<< mx = mx >>= f
  fun x >> y = x >>= (fn _ => y)
  (* fish. *)
  fun f >=> g = fn x => f x >>= g
  fun g <=< f = fn x => f x >>= g

  (* Some of these are names stolen from haskell functions
   * over Functor and Applicative instances. *)
  fun fmap f mx = mx >>= (fn x => return $ f x)
  fun f <$> x = fmap f x
  val liftM = fmap
  fun liftM2 f m1 m2 =
      m1 >>= (fn x1 => m2 >>= (fn x2 => return $ f x1 x2))
  fun liftM3 f m1 m2 m3 =
      m1 >>= (fn x1 => m2 >>= (fn x2 => m3 >>= (fn x3 => return $ f x1 x2 x3)))
  (* Sigh, SML. Why don't you curry more? *)
  fun liftM2' f (m1, m2) =
      m1 >>= (fn x1 => m2 >>= (fn x2 => return $ f (x1, x2)))

  fun ap f x = liftM2 id f x
  fun f <*> x = ap f x

  fun sequence ms =
      foldr (liftM2' (op ::)) (return []) ms

  fun sequence_ ms = foldr (op >>) (return ()) ms

  fun mapM f x = sequence $ map f x
  fun mapM_ f x = sequence_ $ map f x
  fun forM x f = mapM f x
  fun forM_ x f = mapM_ f x

  (* Haskell defines forever as "forever a   = a >> forever a".
   * We can't do that because we are strict *)
  fun forever a = a >>= (fn _ => forever a)

  fun join m = m >>= id
end

(******************** Now for some monads. **********************)

(* The option monad is the canonical first example. *)
structure OptionM : MONAD =
struct
  type 'a m = 'a option
  val return = SOME
  fun x >>= k = Option.mapPartial k x
end

structure IdentityM : MONAD =
struct
  type 'a m = 'a
  val return = id
  fun m >>= f = f m
end

(* The list monad isn't really that useful in SML since we are strict
 * and so you always compute all the possibilities. A stream monad would
 * be handy, though. *)
structure ListM : MONAD =
struct
  type 'a m = 'a list
  fun return x = [x]
  fun xs >>= f = List.concat (map f xs)
end


signature STATE =
sig
  include MONAD
  type state

  (* The core functions. *)
  val runState : 'a m -> state -> 'a * state
  val get : state m
  val put : state -> unit m

  (* Utility functions. *)
  val modify : (state -> state) -> unit m
  val gets : (state -> 'a) -> 'a m
  val evalState : 'a m -> state -> 'a
  val execState : 'a m -> state -> state
  val mapState : ('a * state -> 'b * state) -> 'a m -> 'b m
  val withState : (state -> state) -> 'a m -> 'a m
end

functor StateFn(type t) : STATE =
struct
  type state = t
  type 'a m = state -> 'a * state

  fun return x s = (x, s)
  fun m >>= f = fn s => let val (x, s') = m s
                        in f x s' end

  fun runState m s = m s
  val runState : 'a m -> state -> 'a * state = runState

  fun get s = (s, s)
  fun put s _ = ((), s)

  fun modify f =
      get >>= (fn s => put (f s))
  fun gets f =
      get >>= (fn s => return (f s))
  fun evalState f s = #1 $ runState f s
  fun execState f s = #2 $ runState f s

  fun mapState f m =
      get >>= (fn s =>
      m >>= (fn x =>
      let val (x', s') = f (x, s)
      in put s' >>= (fn _ => return x') end))
  fun withState f m = modify f >>= (fn _ => m)
end

signature IO =
sig
  include MONAD
  type 'a IO = 'a m
  val unsafePerformIO : 'a IO -> 'a

  (* References *)
  val refM : 'a -> 'a ref IO
  val ! : 'a ref -> 'a IO
  val := : 'a ref * 'a -> unit IO

  (* Some simple IO as a proof of concept *)
  val stdIn : TextIO.instream
  val stdOut : TextIO.outstream
  val stdErr : TextIO.outstream
  val openIn : string -> TextIO.instream IO
  val openOut : string -> TextIO.outstream IO
  val closeIn : TextIO.instream -> unit IO
  val closeOut : TextIO.outstream -> unit IO
  val inputLine : TextIO.instream -> string option IO
  val inputLine' : TextIO.instream -> string IO
  val input : TextIO.instream -> string IO
  val inputAll : TextIO.instream -> string IO
  val output : TextIO.outstream -> string -> unit IO
  val print : string -> unit IO
end

structure IO : IO =
struct
  type 'a m = unit -> 'a
  type 'a IO = 'a m

  fun unsafePerformIO m = m ()
  fun return x () = x
  fun m >>= k = fn () => (k (m ())) ()

  fun refM x () = ref x
  fun ! x () = General.! x
  fun x := y = fn () => General.:= (x, y)

  val stdIn = TextIO.stdIn
  val stdOut = TextIO.stdOut
  val stdErr = TextIO.stdErr
  fun openIn s () = TextIO.openIn s
  fun openOut s () = TextIO.openOut s
  fun closeIn s () = TextIO.closeIn s
  fun closeOut s () = TextIO.closeOut s
  fun inputLine s () = TextIO.inputLine s
  fun inputLine' s = inputLine s >>= return o valOf
  fun input s () = TextIO.input s
  fun inputAll s () = TextIO.input s
  fun output stream s () = TextIO.output (stream, s)
  fun print s () = TextIO.print s
end

structure IOM = IO :> MONAD where type 'a m = 'a IO.IO


(* This really is prettier with typeclasses. Le sigh. *)
structure IOMonadUtil = MonadUtil(IO)

structure Test =
struct
local
  open IO
  open IOMonadUtil
in

  fun println s = print (s ^ "\n")
  val main = mapM_ print [ "one ", "two ", "three ", "four\n" ]

  val main2 =
      refM "hello " >>= (fn r =>
      !r >>= (fn s =>
      print s >>
      println "world"))

  fun prompt s = println s >> inputLine' stdIn

  fun exclaim s = s ^ "!"
  val inputmain = prompt "something? " >>= println o exclaim

  val mainloop : unit IO = forever $ println "loool!"

end
end

val run = IO.unsafePerformIO
