(* variable-queue.sml (inspired by CMU 15-410's variable_queue.h)
 *
 * An implementation of generic, imperative, mutable, intrusive linked
 * lists for SML. Generic Intrusive linked lists are a trick that C
 * kernel hackers really love: instead of allocating cons cells when
 * you want to put things on lists, you embed list link fields (the
 * prev and next pointers) inside the objects.
 *
 * Since you want to be able to handle different kinds of objects and
 * allow objects to be on multiple lists at once, you want to be able
 * to embed multiple link fields in objects and have the library code
 * be generic over both the object type and the link field being
 * used. In C, this is traditionally done with macros. In SML, we can
 * do it safely. We can paramterize the list operations over the type
 * of objects and a function that projects from an object to a list
 * link field inside of it.
 *
 * There are a number of possible design trade-offs to make in
 * deciding out how to parameterize the library over the object and
 * the link field.
 *
 *   1) Implement the library as polymorphic functions that take the
 * link projection function as an argument. This design most closely
 * mirrors variable_queue.h, but is burdensome, especially since the
 * list elements need to be recursive types, and thus record
 * projection functions can't be used for projecting.
 *   2) Be polymorphic, but take the link projection function as an
 * argument when creating the list head and store it there. This has
 * the minor disadvantage that then the head needs to be passed in as
 * an argument to get_next and get_prev. (This is a lot more annoying
 * in the implementation than in actual use.) Furthermore, queues that
 * hold the same sorts of objects will all have the same type,
 * regardless of what traversal field they use. It would be nice to be
 * able to distinguish them in the type system.
 *
 *   3) Functorize over the type and the link projection function. One
 * downside of this is that since the object type must be declared
 * before the functor is instantiated, the link field must be declared
 * polymorphically outside of the functor. Since the VariableQueue
 * functor needs to actually be able to work with the type, this
 * prevents the link type from being made abstract to clients. (The
 * trick I used in fast-vector.sml doesn't work because SML doesn't
 * have functor signatures. We can go part way and hide the
 * constructors after the definition of VariableQueue.) Thanks to
 * generative functors, we then get the advantage that queues using
 * different link fields have different types, which is pretty nice.
 * There is one catch, though: objects may need to include the head of
 * a queue of the same type of objects (consider a process control
 * block that needs to maintain a list of its children processess). To
 * deal with this, we declare the head type polymorphically like the
 * link type, and expose two versions of the library. VariableQueue,
 * which keeps the head type abstract, should be used whenever the
 * queue will not be embedded in the object type it contains, and
 * VariableQueueNestable, which exposes the head type, which placed in
 * the object type it holds.
 *
 * We went with option 3. It is not really clear that this was a
 * particularly better choice than option 2.
 *
 * In addition to reducing memory allocations (which we usually don't
 * worry about in ML) and avoiding the possibility of memory
 * allocation failure (which we *can't* worry about in ML, but which
 * is critical in kernel level programming), intrusive linked lists
 * has another advantage that might make this library worthwhile: no
 * matter how you acquired a handle to an object, you can find where
 * it is on all of the lists it is on in constant time. This would be
 * useful for doing things like LLVM style use-def chains in a
 * compiler.
*)

(* Polymorphic link and head types, for use in declaring objects that
 * use VQ. *)
structure VQLink =
struct
  datatype 'a link = L of {prev: 'a option ref, next: 'a option ref}
  (* Since an invariant is that either both head and tail are NONE
   * or both are SOME, we could require that in our type by having
   * a single ref option. That would get us some nice guarantees, but
   * seemed like more of a hassle to write the code for. *)
  datatype 'a head = H of {head: 'a option ref, tail: 'a option ref}
end

(* VQ interface. *)
signature VARIABLE_QUEUE =
sig
  type elem
  type head
  type link

  (* Create new list heads and links. *)
  val new_head : unit -> head
  val new_link : unit -> link

  (* Primitive list traversal functions. *)
  val get_head : head -> elem option
  val get_tail : head -> elem option
  val get_next : elem -> elem option
  val get_prev : elem -> elem option

  (* Versions that instead raise an exception if the pointer is NONE. *)
  val get_head' : head -> elem
  val get_tail' : head -> elem
  val get_next' : elem -> elem
  val get_prev' : elem -> elem

  (* Basic list manipulations. *)
  val insert_front : head -> elem -> unit
  val insert_tail : head -> elem -> unit
  (* insert_{after,before} q inq new inserts new {after,before} inq in q *)
  val insert_after : head -> elem -> elem -> unit
  val insert_before : head -> elem -> elem -> unit
  val remove : head -> elem -> unit
  (* concat q1 q2 moves the contents of q2 to the back of q1, leaving q2 empty. *)
  val concat : head -> head -> unit

  (* List processing operations.
   * Note that map doesn't really make much sense here. *)
  val app : (elem -> unit) -> head -> unit
  val foldl : (elem * 'b -> 'b) -> 'b -> head -> 'b
  val foldr : (elem * 'b -> 'b) -> 'b -> head -> 'b
end

(* Interface for objects that live on VQ lists. *)
signature VQ_ELEM =
sig
  type elem
  val get_link : elem -> elem VQLink.link
end

(* A VQ implementation that exposes that the head type is
 * VQLink.head. *)
functor VariableQueueNestable(Elem : VQ_ELEM)
        :> VARIABLE_QUEUE where type elem = Elem.elem
                            and type link = Elem.elem VQLink.link
                            and type head = Elem.elem VQLink.head
=
struct
  local
      open VQLink
  in

  type elem = Elem.elem
  type head = elem VQLink.head
  type link = elem VQLink.link
  val get_link = Elem.get_link

  fun new_head () = H {head=ref NONE, tail=ref NONE}
  fun new_link () = L {prev=ref NONE, next=ref NONE}

  fun get_head (H {head, ...}) = !head
  fun set_head (H {head, ...}) new_head = head := new_head
  fun get_tail (H {tail, ...}) = !tail
  fun set_tail (H {tail, ...}) new_tail = tail := new_tail
  fun get_next nobe =
      let val (L {next, ...}) = get_link nobe in !next end
  fun set_next nobe new_next =
      let val (L {next, ...}) = get_link nobe
      in next := new_next end
  fun get_prev nobe =
      let val (L {prev, ...}) = get_link nobe in !prev end
  fun set_prev nobe new_prev =
      let val (L {prev, ...}) = get_link nobe
      in prev := new_prev end

  (* Stupid value restriction. *)
  fun get_head' h = valOf (get_head h)
  fun get_tail' h = valOf (get_tail h)
  val get_next' = valOf o get_next
  val get_prev' = valOf o get_prev

  fun insert_front head elem =
      (set_prev elem NONE;
       set_next elem (get_head head);
       (case get_head head of
           SOME head' => set_prev head' (SOME elem)
         (* the list must be empty; set the tail too *)
         | NONE => set_tail head (SOME elem));
       set_head head (SOME elem))
  fun insert_tail head elem =
      (set_next elem NONE;
       set_prev elem (get_tail head);
       (case get_tail head of
           SOME tail' => set_next tail' (SOME elem)
         (* the list must be empty; set the head too *)
         | NONE => set_head head (SOME elem));
       set_tail head (SOME elem))
  fun insert_after head inq toinsert =
      (set_prev toinsert (SOME inq);
       set_next toinsert (get_next inq);
       (case get_next inq of
            SOME next => set_prev next (SOME toinsert)
          (* inq must be the tail *)
          | NONE => set_tail head (SOME toinsert));
       set_next inq (SOME toinsert))
  fun insert_before head inq toinsert =
      (set_next toinsert (SOME inq);
       set_prev toinsert (get_prev inq);
       (case get_prev inq of
            SOME prev => set_next prev (SOME toinsert)
          (* inq must be the head *)
          | NONE => set_head head (SOME toinsert));
       set_prev inq (SOME toinsert))

  fun remove head elem =
      ((case get_prev elem of
            SOME prev => set_next prev (get_next elem)
          (* elem must be the head *)
          | NONE => set_head head (get_next elem));
       (case get_next elem of
            SOME next => set_prev next (get_prev elem)
          (* elem must be the tail *)
          | NONE => set_tail head (get_prev elem));
       set_next elem NONE;
       set_prev elem NONE)

  fun concat head1 head2 =
      ((case (get_tail head1, get_head head2) of
            (NONE, _) => 
            (set_head head1 (get_head head2);
             set_tail head1 (get_tail head2))
          | (SOME tail1', SOME head2') =>
            (set_next tail1' (SOME head2');
             set_prev head2' (SOME tail1');
             set_tail head1 (get_tail head2))
          | (SOME _, NONE) => ());
       set_head head2 NONE;
       set_tail head2 NONE)

  fun app f head =
      let fun loop (SOME x) = let val () = f x in loop (get_next x) end
            | loop NONE = ()
      in loop (get_head head) end

  fun foldl f z head =
      let fun loop z (SOME x) = loop (f (x, z)) (get_next x)
            | loop z NONE = z
      in loop z (get_head head) end
  fun foldr f z head =
      let fun loop z (SOME x) = loop (f (x, z)) (get_prev x)
            | loop z NONE = z
      in loop z (get_tail head) end


  end
end

(* Hide the constructors from everybody but the real implementation. *)
structure VQLink : sig type 'a link type 'a head end = VQLink

(* A VQ implementation that hides the type of head. *)
functor VariableQueue(Elem : VQ_ELEM)
        :> VARIABLE_QUEUE where type elem = Elem.elem
                            and type link = Elem.elem VQLink.link
=
struct
  structure Q = VariableQueueNestable(Elem)
  open Q
end

structure VQTest =
struct
  datatype test = Test of {id: int, link: test VQLink.link}
  structure Q = VariableQueue(struct type elem = test
                                     val get_link = fn Test {link, ...} => link end)

  fun new_test n = Test {id = n, link = Q.new_link ()}

  fun print_vq q = Q.app (fn Test {id, ...} => print (Int.toString id ^ "\n")) q
  fun to_list q = Q.foldr (fn (Test {id, ...}, l) => id :: l) [] q

  fun from_list l =
      let val q = Q.new_head ()
          fun add_num i = Q.insert_tail q (new_test i)
          val () = app add_num l
      in q end

  fun test () =
      let val head = from_list [1,2,3,4,5]
          val third = Q.get_next' (Q.get_next' (Q.get_head' head))
          val () = Q.insert_after head third (new_test 42)
          val () = Q.insert_after head (Q.get_tail' head) (new_test 1337)
          val () = Q.insert_before head third (new_test ~5)
          val () = Q.remove head third
          val () = Q.remove head (Q.get_head' head)
          val () = Q.concat head (from_list [7,8,9])
      in head end
end
