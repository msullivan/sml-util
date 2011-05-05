(* Inspired by
 * http://existentialtype.wordpress.com/2011/05/01/of-course-ml-has-monads/ *)

infixr 0 $
infixr >>=
infixr >>
infixr =<<
infixr >=>

fun f $ x = f x
fun id x = x
fun const x y = x

signature MONAD =
sig
  type 'a monad
  val return : 'a -> 'a monad
  val bind : 'a monad -> ('a -> 'b monad) -> 'b monad
end

structure OptionM : MONAD =
struct
  type 'a monad = 'a option
  val return = SOME
  fun bind x k = Option.mapPartial k x
end

signature IO =
sig
  include MONAD
  type 'a IO = 'a monad
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
signature IO = IO

structure IO : IO =
struct
  type 'a monad = unit -> 'a 
  type 'a IO = 'a monad
  fun unsafePerformIO f = f ()

  fun return x () = x
  fun bind mx k () = (k (mx ())) ()

  val refM = fn x => fn () => ref x
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
  fun inputLine' s = bind (inputLine s) (return o valOf)
  fun input s () = TextIO.input s
  fun inputAll s () = TextIO.input s
  fun output stream s () = TextIO.output (stream, s)
  val print = fn s => fn () => TextIO.print s
end

structure IOM = IO :> MONAD where type 'a monad = 'a IO.IO

functor MonadUtil(M : MONAD) =
struct
local
  open M
in

  fun mx >>= f = bind mx f
  fun f =<< mx = bind mx f
  fun x >> y = x >>= (fn _ => y)
  fun f >=> g = fn x => f x >>= g

  fun sequence ms =
      let fun k (m, m') =
              m >>= (fn x =>
              m' >>= (fn xs =>
              return (x::xs)))
      in foldr k (return []) ms end

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
end

(* This really is prettier with typeclasses. Le sigh. *)
structure IOMonadUtil = MonadUtil(IO)
open IO
open IOMonadUtil

structure Test =
struct
  fun println s = print (s ^ "\n")
  val main = mapM_ print [ "one ", "two ", "three ", "four\n" ]

  val main2 =
      refM "hello " >>= (fn r =>
      !r >>= (fn s =>
      print s >>
      println "world"))

  val mainloop : unit IO = forever $ println "loool!"

end

val run = unsafePerformIO
