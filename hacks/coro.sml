signature CORE_CORO =
sig
    type ('y,'r,'f) coro
    datatype ('y,'f) result = Yield of 'y | Finish of 'f

    val mk_coro : (('y -> 'r) -> 'r -> 'f) -> ('y,'r,'f) coro
    val resume : ('y,'r,'f) coro -> 'r -> ('y,'f) result

end
signature CORO =
sig
    include CORE_CORO

    exception StopIteration
    type 'a gen = ('a, unit, unit) coro
    val mk_gen : (('a -> unit) -> unit) -> 'a gen

    val next : 'a gen -> 'a option
    val nextE : 'a gen -> 'a
end

structure CoreCoro :> CORE_CORO =
struct
    structure Cont = SMLofNJ.Cont
    type 'a cont = 'a Cont.cont
    datatype ('y,'f) result = Yield of 'y | Finish of 'f

    type ('y,'r,'f) coro = {
        yield_cont: ('y,'f) result cont option ref,
        resume_cont: 'r cont option ref
    }

    fun get r =
      let val x = valOf (!r)
      in r := NONE;
         x
      end

    fun transfer from to x =
      Cont.callcc (
          fn k =>
             (from := SOME k;
              Cont.throw (get to) x))

    fun mk_coro body =
      let
          val yield_cont = ref NONE
          val resume_cont = ref NONE

          val yield = transfer resume_cont yield_cont

          fun body' x =
            (yield (Finish (body (fn z => yield (Yield z)) x));
             raise Fail "resuming finished coro!")

      in
          (* set up initial resume cont *)
          Cont.callcc
              (fn k_esc : unit cont =>
                  let val x = Cont.callcc (fn k =>
                                              (resume_cont := SOME k;
                                               Cont.throw k_esc ()))
                  in body' x end);
          (* and we're ready *)
          {yield_cont=yield_cont, resume_cont=resume_cont}
      end

    fun resume {yield_cont, resume_cont} x =
      transfer yield_cont resume_cont x
end

functor CoroFn(CoreCoro : CORE_CORO) :> CORO =
struct
  open CoreCoro

  exception StopIteration
  type 'a gen = ('a, unit, unit) coro

  fun mk_gen body = mk_coro (fn yield => fn () => body yield)

  fun next gen =
    (case resume gen () of
         Yield x => SOME x
       | Finish () => NONE)
  fun nextE gen =
    (case resume gen () of
         Yield x => x
       | Finish () => raise StopIteration)


end

structure Coro = CoroFn(CoreCoro)

(****************************************)
(* functor? *)
structure CoroUtil =
struct
local
    open Coro
in
  fun collect gen =
    (case next gen of
         NONE => []
       | SOME x => x :: collect gen)
  fun take 0 gen = []
    | take n gen =
    (case next gen of
         NONE => []
       | SOME x => x :: take (n-1) gen)

  fun foldl f z gen =
    (case next gen of
         NONE => z
       | SOME x => foldl f (f (x, z)) gen)
  fun foreach gen f = foldl (fn (x, ()) => f x) () gen

end

end

(******************)

structure CoroTest =
struct
local
    open Coro
in
  fun stupid_gen' yield =
    (yield 1;
     yield 2;
     yield 3;
     yield 4;
     ())
  fun stupid_gen () = mk_gen stupid_gen'

  fun nats' yield =
    let fun loop i = (yield i; loop (i+1))
    in loop 0 end
  fun nats () = mk_gen nats'


  fun is_prime n =
    let
        val sq = Real.ceil (Math.sqrt (Real.fromInt n))
        fun loop i = if i > sq then true else
                     n mod i <> 0 andalso loop (i+1)
    in n = 2 orelse n >= 2 andalso loop 2 end

  fun primes' yield =
    let val () = yield 2
        fun loop i =
          (if is_prime i then yield i else ();
           loop (i+2))
    in loop 3 end
  fun primes () = mk_gen primes'

  fun primes2' yield =
    CoroUtil.foreach (nats ()) (
        fn i => if is_prime i then yield i else ())
  fun primes2 () = mk_gen primes2'



end
end
