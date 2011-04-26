(* An implementation of finalizers built without explicit language 
 * support on top of weak pointers. This only works under SML/NJ.
 *
 * This scheme was devised in conversation between Karl Crary,
 * Luke Zarko, and Michael Sullivan.
 * (It is also mentioned in the SML/NJ weak pointer documentation,
 *  so we apparently weren't the first people to think of it.)
 *)

signature FINALIZE =
sig
  type 'a finalized
  val make_finalized : ('a -> unit) -> 'a -> 'a finalized
  val read : 'a finalized -> 'a
end

structure Finalize :> FINALIZE =
struct
  structure Weak = SMLofNJ.Weak
  (* We use a ref because they have a strong notion of object identity
   * and we can be pretty sure that the compiler can't do anything
   * to optimize the boxing away. We don't ever modify the contents
   * of the ref. *)
  type 'a finalized = 'a ref

  (* table entries consist of a weak pointer and a finalizer closure
   * that finalizes the object. *)
  type table_entry = Weak.weak' * (unit -> unit)
  val table : table_entry list ref = ref nil

  (* There might be a concurrency hazard here, if we get our gc
   * signal in the middle of this operation. However I think under
   * the SML/NJ runtime this is not possible since it only checks
   * for interrupts at the start of "extended basic blocks". *)
  fun make_finalized f x =
      let val finalized = ref x
          val entry = (Weak.weak' finalized, fn () => f x)
          val () = table := entry :: (!table)
      in finalized end

  val read = op !

  fun gc () =
      let (* Since the finalizers might create new finalized objects,
           * we need to properly deal with that. This is handled by
           * clearing off the list, running the finalizers and
           * filtering the list, and then appending the new list to
           * the filtered old list and storing it back. *)
          val l = !table
          val () = table := nil
          fun check_finalizer (weakp, finalizer) =
              if Weak.strong' weakp then true
              else (finalizer (); false)
          val l' = List.filter check_finalizer l
      in table := l' @ (!table) end

  val _ = Signals.setHandler (Signals.sigGC,
                              Signals.HANDLER (fn (_, _, k) => (gc (); k)))
end
