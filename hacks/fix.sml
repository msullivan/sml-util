(* Various implementations of a fixed point combinator in SML *)

signature FIX =
sig
  val fix : (('a -> 'b) -> ('a -> 'b)) -> ('a -> 'b)
end

(* Fix based on having recursive bindings built into the language *)
structure FunFix :> FIX =
struct
  fun fix f x = f (fix f) x
end

(* Fix based on reference cells *)
structure RefFix :> FIX =
struct
  val fix = fn f => let
      val cell = ref NONE
      val f' = f (fn x => valOf (!cell) x)
      val () = cell := SOME f'
  in f' end
end

(* Fix based on the Y combinator and recursive types *)
structure RecFix :> FIX =
struct
  datatype 'a urec = Rec of 'a urec -> 'a
  fun unRec (Rec x) = x

  val fix = fn f => let
      val f' = Rec (fn x => f (fn z => unRec x x z))
  in unRec f' f' end
end

(* Fix based on exceptions *)
(* N.B. Not named ExnFix because exn stands for extensible *)
structure ExceptionFix :> FIX =
struct
  val fix = fn f => let
      exception E of ('a -> 'b) -> 'a -> 'b
      val recurse = fn y => fn z => y z handle E x => f (x y) z
  in recurse (fn _ => raise E recurse) end
end

(* Fix based on the Y combinator and the extensible type *)
structure ExnFix :> FIX =
struct
  (* This is basically the same as the recursive type one *)
  val fix = fn f => let
      exception Rec of exn -> ('a -> 'b)
      fun unRec (Rec x) = x
      val f' = Rec (fn x => f (fn z => unRec x x z))
  in unRec f' f' end
end

(* Mutual recursion fix point! *)
signature FIX2 =
sig
  val fix2 : (('c -> 'd) -> ('a -> 'b)) -> (('a -> 'b) -> ('c -> 'd)) ->
             (('a -> 'b) * ('c -> 'd))
end

(* Mutual recursion fix point based on fun *)
structure FunFix2 : FIX2 =
struct
  fun fix2 f g =
      let fun f' x = f g' x
          and g' y = g f' y
      in (f', g') end
end


functor FixTest (structure Fix : FIX) =
struct
  local
      val fact' = fn f => fn n => case n of 0 => 1
                                          | n => n * (f (n-1))
  in
  val fact = Fix.fix fact'
  end
end



structure FunTest = FixTest(structure Fix = FunFix)
val n1 = FunTest.fact 10
structure RefTest = FixTest(structure Fix = RefFix)
val n2 = RefTest.fact 10
structure RecTest = FixTest(structure Fix = RecFix)
val n3 = RecTest.fact 10
structure ExceptionTest = FixTest(structure Fix = ExceptionFix)
val n4 = ExceptionTest.fact 10
structure ExnTest = FixTest(structure Fix = ExnFix)
val n5 = ExnTest.fact 10
