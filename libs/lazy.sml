(* There are a bunch of ways to do this. Should I benchmark?
 * Should I use something existing? *)

signature LAZY =
sig
    type 'a susp
    val delay : (unit -> 'a) -> 'a susp
    val eager : 'a -> 'a susp
    val force : 'a susp -> 'a
end

structure LazyFn :> LAZY =
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

structure LazyTag : LAZY =
struct
  datatype 'a tag = Susp of unit -> 'a | V of 'a
  datatype 'a susp = L of 'a tag ref

  fun delay f = L (ref (Susp f))
  fun eager v = L (ref (V v))

  fun force (L (ref (V x))) = x
    | force (L (r as ref (Susp f))) =
      let val x = f ()
          val () = r := V x
      in x end
end

structure LazyNot :> LAZY =
struct
  type 'a susp = 'a

  fun delay f = f ()
  fun eager v = v
  fun force susp = susp
end

structure Susp = LazyTag
