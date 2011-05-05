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
  val gc : unit -> unit
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

  fun gc_handler () =
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

  (* It seems that sigGC never actually happens? *)
  fun init () = 
      Signals.setHandler
          (Signals.sigGC,
           Signals.HANDLER (fn (_, _, k) => (gc_handler (); k)))
  val _ = init ()

  fun gc () = (SMLofNJ.Internals.GC.doGC 0; gc_handler ())
end


(* A very simple wrapper around some of the TextIO functions that
 * will automatically close files once all of the references are
 * dropped. This ought to be fleshed out. *)
signature SAFE_TEXT_IO =
sig
  type instream
  type outstream

  val openIn  : string -> instream
  val openOut : string -> outstream
  val stdIn  : instream
  val stdOut : outstream
  val stdErr : outstream

  val output : outstream * string -> unit
  val inputLine : instream -> string option
  val input : instream -> string option
  val closeIn : instream -> unit
  val closeOut : outstream -> unit
end

structure SafeTextIO :> SAFE_TEXT_IO =
struct
  structure F = Finalize
  structure IO = TextIO

  type instream = IO.instream F.finalized
  type outstream = IO.outstream F.finalized

  fun wrap_in s = F.make_finalized IO.closeIn s
  fun wrap_out s = F.make_finalized IO.closeOut s

  (* These might fail because there are too many open file
   * descriptors, in which case we want to trigger a gc and
   * try one more time. Really, we should probably actually
   * check the cause of the exception... *)
  fun openIn fname = wrap_in
                         ((IO.openIn fname)
                          handle _ => (F.gc (); IO.openIn fname))
  fun openOut fname = wrap_out
                          ((IO.openOut fname)
                           handle _ => (F.gc (); IO.openOut fname))

  val stdIn = wrap_in IO.stdIn
  val stdOut = wrap_out IO.stdOut
  val stdErr = wrap_out IO.stdErr
  fun output (s, v) = IO.output (F.read s, v)
  val inputLine = IO.inputLine o F.read
  val input = IO.inputLine o F.read
  val closeIn = IO.closeIn o F.read
  val closeOut = IO.closeOut o F.read
end

(* Do some simple testing. *)
structure SafeIOTesting =
struct
  fun do_thing i =
      let 
          val s = Int.toString i
          val () = print (s ^ "\n")
          val f = SafeTextIO.openOut ("/tmp/" ^ s ^ ".txt")
      in SafeTextIO.output (f, s) end

  fun test () =
      let fun loop i = (do_thing i; loop (i+1))
      in loop 0 end

end
