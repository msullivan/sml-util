signature AMB =
sig
    exception AmbFail
    val new_amb : unit -> 'a list -> 'a
end

structure Amb :> AMB =
struct
   exception AmbFail
   open SMLofNJ.Cont

   datatype 'a backtrack = BChoice of 'a | BBacktrack

   fun 'a new_amb () =
       let
           val conts : 'a backtrack cont list ref = ref nil
                       
           fun amb nil = 
               (case conts
                 of (ref nil) => raise AmbFail
                  | (ref (last::rest)) => 
                    (conts := rest;
                     throw last BBacktrack))
             | amb (x::xs) =
               (case (callcc
                          (fn cont => (conts := cont::(!conts); BChoice x)))
                 of BChoice y => y
                  | BBacktrack => amb xs)
       in
           amb
       end
end

fun test0 () =
    let
        val amb = Amb.new_amb ()
        val x = amb [1, 2, 3, 4, 5]
        val _ = if x <> 4 then amb nil else 0
    in
        x
    end

fun test1 () =
    let
        val amb = Amb.new_amb ()
        val x = amb [1, 2, 3]
        val y = amb [4, 5, 6]
        val _ = if x*y <> 10 then amb nil else 0
    in
        (x, y)
    end
