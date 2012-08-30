(* This is just the code from Andrzej Filinski's paper
 * "Representing Monads", made to work with modern SML/NJ
 * and my monad.sml. I also wrote some "direct" implementations
 * of reify and reflect for various common monads in terms of
 * different SML effects. The implementation for List uses my
 * amb.sml.
 * I also got rid of the uses of unsafe casts in the monad
 * representation code. This code is now entirely safe, and the
 * only non-standard feature it uses is call/cc.
 *)

infixr 0 $ infix 1 >>= >> infixr 1 =<< >=> <=< infix 4 <$> <*> fun f $ x = f x

signature ESCAPE =
sig
    type void
    val coerce : void -> 'a
    val escape : (('a -> void) -> 'a) -> 'a
end

structure Escape : ESCAPE =
struct
  open SMLofNJ.Cont
  datatype void = VOID of void
  fun coerce (VOID v) = coerce v
  fun escape f = callcc (fn k => f (fn x => throw k x))
end

signature CONTROL =
sig
  type ans
  val reset : (unit -> ans) -> ans
  val shift : (('a -> ans) -> ans) -> 'a
end

functor Control(type ans) : CONTROL =
struct
  open Escape
  exception MissingReset
  val mk : (ans -> void) ref = ref (fn _ => raise MissingReset)

  fun abort x = coerce (!mk x)

  type ans = ans
  fun reset t =
      escape
      (fn k => let val m = !mk in
                   mk := (fn r => (mk := m; k r));
                   abort (t ()) end)
  fun shift h =
      escape
      (fn k => abort (
               h (fn v => reset (fn () => coerce (k v)))))
end

structure IntCtrl = Control(type ans = int)
val test_val =
    let open IntCtrl
    in 1 + reset (fn () => 2 * shift (fn k => k (k 10))) end

signature RMONAD =
sig
  structure M : MONAD
  val reflect : 'a M.m -> 'a
  val reify : (unit -> 'a) -> 'a M.m
end


(* I got rid of the unsafe casts in the original code from the paper
 * by using an interface that builds pairs of injection/projection
 * functions. *)
(* This interface inspired by the mlton wiki UniversalType page. *)
signature UNIVERSAL =
sig
  type u
  exception UniversalTypeMismatch
  val embed : unit -> ('a -> u) * (u -> 'a)
end

structure Universal :> UNIVERSAL =
struct
  type u = exn
  exception UniversalTypeMismatch

  fun embed () =
      let exception E of 'a
          val to_u = E
          fun from_u (E x) = x
            | from_u _ = raise UniversalTypeMismatch
      in (to_u, from_u) end
end


functor Represent (M : MONAD) : RMONAD =
struct
  structure C = Control (type ans = Universal.u M.m)

  structure M = M
  open M

  structure MU = MonadUtil(M) open MU

  fun reflect m = C.shift (fn k => m >>= k)
  fun reify t =
      let val (to_u, from_u) = Universal.embed ()
      in (* Morally, this should just be:
          * C.reset (fn () => return (t ())),
          * but we need to inject into the universal type in order to
          * make the typing for reset work out, and then project back
          * out of it. *)
          from_u <$> (C.reset (fn () => return (to_u (t ()))))
      end
end

(* Some manual implementations of reify/reflect for some of
 * the monads. *)
structure ErrorRepManual : RMONAD =
struct
  structure M = Error
  open Error
  fun reify thunk = (Success (thunk ())
                     handle e => Failure e)

  fun reflect (Success x) = x
    | reflect (Failure e) = raise e
end

functor StateRepManual(S : STATE) : RMONAD =
struct
  structure M = S
  val cell : M.state option ref = ref NONE
  fun store s = cell := SOME s
  fun get () = valOf (!cell)

  fun reify thunk =
      fn s => (store s;
               (thunk (), get ()))
  fun reflect f =
      let val (x, s) = f (get ())
          val () = store s
      in x end

end

structure ListRepManual : RMONAD =
struct
   structure M = ListM
   val reflect = Amb.amb
   val reify = Amb.collect
end


(* Now some test code *)

(* Error *)
structure ErrorRep = Represent(Error)

local
    open Error ErrorRep
in
(* Definitions of the normal constructs in terms of the underlying
 * monadic type and reify/reflect *)
fun raise' e = reflect (Failure e)
val raise' : exn -> 'a = raise'

fun handle' try fail =
    (case reify try of
         Success x => x
       | Failure e => fail e)
val handle' : (unit -> 'a) -> (exn -> 'a) -> 'a = handle'
end

fun show t =
    handle' (fn () => "OK: " ^ Int.toString (t ()))
            (fn e => "Error: " ^ exnMessage e)
val err_test1 = show (fn () => 1 + 2)
val err_test2 = show (fn () => 1 + raise' (Fail "oops"))

(* Some example code *)
val test =
    handle'
    (fn () => raise' (Fail "hello!"))
    (fn e => print (exnMessage e ^ "\n"))


(* State *)
structure IntState = StateFn(type t = int)
structure IntStateRep = Represent(IntState)
structure IntStateRepManual = StateRepManual(IntState)


fun tick () = IntStateRep.reflect (IntState.modify (fn s => s+1))
fun fetch () = IntStateRep.reflect IntState.get
fun store n = IntStateRep.reflect (IntState.put n)

val state_test1 = IntStateRep.reify
                  (fn () => (store 5; tick();
                             2 * fetch ()))
val state_test1_val = IntState.evalState state_test1 0

(* List *)
structure ListRep = Represent(ListM)

local open ListRep in
(* The original definition of amb in the paper is as follows,
 * but I think the one after it is the same...
 * Am I mistaken? *)
fun amb2 (x, y) = reflect (reify (fn () => x) @
                           reify (fn () => y))
fun amb2 (x, y) = reflect [x, y]
fun fail () = reflect []
end

val list_test1 =
    ListRep.reify (fn () => let val x = amb2 (3, 4) * amb2 (5, 7)
                            in if x >= 20 then x
                               else fail () end)

local open ListRep in
val list_test2 =
    reify (fn () => let val x = reflect [3, 4, 5]
                        val y = reflect ["foo", "bar"]
                    in (x, y) end)
end

(* Cont *)
structure ContRep =
  Represent(ContFn(type ans = string))

local open ContRep in
  fun myescape h =
      reflect (fn c => let fun k a = reflect (fn c' => c a)
                       in reify (fn () => h k) c end)
  fun myshift h =
      reflect (fn c => let fun k a = reflect (fn c' => c' (c a))
                       in reify (fn () => h k) (fn x => x) end)
  fun myreset t = reflect (fn c => c (reify t (fn x => x)))
end

val cont_test1 = ContRep.reify
                     (fn () => 3 + myescape (fn k => 6 + k 1))
                     Int.toString

val cont_test2 = ContRep.reify
                 (fn () => "a" ^ myreset (fn () =>
                                             "b" ^ myshift (fn k =>
                                                               k (k "c"))))
                 (fn x => x)
