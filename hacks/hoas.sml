(* An implementation of a higher order abstract syntax based untyped
 * lambda calculus. As it turns out, while you can use HOAS in a language
 * like SML, and you can implement an evaluator, that's about it. *)

signature HOAS_LAMBDA_CALC =
sig
  type expr
  val eval : expr -> expr
  val churchNumEval : expr -> int
  val \ : (expr -> expr) -> expr
  val $$ : expr * expr -> expr
end

structure HOASLambdaCalc :> HOAS_LAMBDA_CALC =
struct
  datatype expr =
           App of expr * expr
         | Lam of expr -> expr
         (* So that we can actually get some data out at the end, 
          * we have a number arm. *)
         | Num of int

  fun eval (App (e1, e2)) =
      (case eval e1 of Lam f => eval (f e2)
                     | _ => raise Fail "applying to non-fun")
    | eval e = e

  fun churchNumEval e =
      let fun getNumber e =
              (case eval e of
                   Num n => n
                 | _ => raise Fail "not a number")
          val izero = Num 0
          fun isucc e = Num (1 + getNumber e)
      in getNumber (App (App (e, Lam isucc), izero)) end

  val \ = Lam
  infix 9 $$
  val (op $$) = App
end

structure Testing =
struct
  local
      infix 9 $$
      open HOASLambdaCalc
  in

  val run = churchNumEval
  val z = \(fn s => \(fn z => z))
  val s = \(fn n => \(fn s => \(fn z =>
            s $$ (n $$ s $$ z))))

  fun makeChurchNum 0 = z
    | makeChurchNum n = s $$ makeChurchNum (n-1)
  fun run1 e n = run (e $$ makeChurchNum n)
  fun run2 e n m = run (e $$ makeChurchNum n $$ makeChurchNum m)


  val id = \(fn z => z)
  val t = \(fn x => \(fn y => x))
  val f = \(fn x => \(fn y => y))

  val add = \(fn n => \(fn m => n $$ s $$ m))
  val mul = \(fn n => \(fn m => n $$ (add $$ m) $$ z))
  (* This is wacky. *)
  val exp = \(fn n => \(fn m => m $$ n))

  val iszero = \(fn n => n $$ \(fn _ => f) $$ t)

  fun pair x y = \(fn f => f $$ x $$ y)
  fun fst z = z $$ \(fn x => \(fn y => x))
  fun snd z = z $$ \(fn x => \(fn y => y))

  val pred =
    \(fn n => fst (
              n $$
              \(fn p => pair (snd p) (s $$ snd p)) $$
              pair z z))

  val Y = \(fn f =>
            \(fn x => (f $$ (x $$ x))) $$
            \(fn x => (f $$ (x $$ x))))

  val fib =
      Y $$
      \(fn f => \(fn n =>
        (iszero $$ n) $$ z $$
        ((iszero $$ (pred $$ n)) $$ (s $$ z) $$
         add $$ (f $$ (pred $$ n)) $$ (f $$ (pred $$ (pred $$ n))))))

  val test = run1 fib 10

  end
end

