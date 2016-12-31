(* There are a bunch of ways to do this. Should I benchmark?
 * Should I use something existing? *)

signature LAZY =
sig
    type 'a susp
    val delay : (unit -> 'a) -> 'a susp
    val eager : 'a -> 'a susp
    val force : 'a susp -> 'a
end

structure Lazy :> LAZY =
struct
  type 'a susp = (unit -> 'a) ref

  fun dummy () = raise Fail "uhoh"
  fun delay f =
    let val cell = ref dummy
        fun thunk () =
          let val v = f ()
              val () = cell := (fn () => v)
          in v end
        val () = cell := thunk
    in cell end

  fun eager v = ref (fn () => v)

  fun force susp = (!susp) ()
end
