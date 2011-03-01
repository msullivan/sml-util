signature TIMEOUT =
sig
  exception Timeout

  (* Run a function with a timeout. *)
  val runWithTimeout : Time.time -> ('a -> 'b) -> 'a -> 'b option

  (* Run a function with a timeout, raising Timeout if it triggers *)
  val runWithTimeoutExn : Time.time -> ('a -> 'b) -> 'a -> 'b

end

structure Timeout :> TIMEOUT =
struct
  exception Timeout

  fun finally f final =
      f () before ignore (final ())
      handle e => (final (); raise e)

  fun runWithTimeout t f x =
      let val timer = SMLofNJ.IntervalTimer.setIntTimer
          fun cleanup () = 
              (timer NONE;
               Signals.setHandler (Signals.sigALRM, Signals.IGNORE); ())

          val ret = ref NONE
          fun doit k =
              let fun handler _ = k
                  val _ = Signals.setHandler (Signals.sigALRM,
                                              Signals.HANDLER handler)
                  val () = timer (SOME t)
              in ret := SOME (f x) end
          val () = finally (fn () => SMLofNJ.Cont.callcc doit) cleanup
      in !ret end

  fun runWithTimeoutExn t f x =
      case runWithTimeout t f x
           of SOME x => x
            | NONE => raise Timeout
end
