signature AMB =
sig
    exception AmbFail
    val amb : 'a list -> 'a
end

structure Amb :> AMB =
struct
   exception AmbFail

   open SMLofNJ.Cont

   val state : unit cont ref =
       ref (callcc (fn escape : unit cont cont =>
                       (callcc (fn k => throw escape k);
                        raise AmbFail)))

   fun amb [] = throw (!state) ()
     | amb (x::xs) =
       let val old = !state
       in callcc (fn escape =>
                     (callcc (fn k => (state := k; throw escape x));
                      state := old;
                      throw escape (amb xs)))
       end
end

fun test0 () =
    let
        val amb = Amb.amb
        val x = amb [1, 2, 3, 4, 5]
        val _ = if x <> 4 then amb nil else 0
    in
        x
    end

fun test1 () =
    let
        val amb = Amb.amb
        val x = amb [1, 2, 3]
        val y = amb [4, 5, 6]
        val _ = if x*y <> 10 then amb nil else 0
    in
        (x, y)
    end

fun test2 () =
    let
        val amb = Amb.amb
        val x = amb [ 2, 3, 4, 5 ]
        val y = amb [ "a", "aaaaa", "aaaaaaa" ]
    in
        if x <> (size y) then amb nil else y
    end
