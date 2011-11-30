signature FACT =
sig
  val fact : int -> int
end

structure FactMatch : FACT =
struct
  fun fact 0 = 1
    | fact n = n * fact (n-1)
end

(* Some testing of inlining, based on the most basic implementation *)
structure FactFun : FACT =
struct
  fun mul (n, m) = n * m
  fun fact 0 = 1
    | fact n = mul (n, fact (n-1))
end

structure FactFunCurry : FACT =
struct
  fun mul n m = n * m
  fun fact 0 = 1
    | fact n = mul n (fact (n-1))
end

structure FactFun5 : FACT =
struct
  fun mul5 (n, m) = n * m
  fun mul4 nm = mul5 nm
  fun mul3 nm = mul4 nm
  fun mul2 nm = mul3 nm
  fun mul1 nm = mul2 nm
  fun fact 0 = 1
    | fact n = mul1 (n, fact (n-1))
end

structure FactFunInteger : FACT =
struct
  fun fact 0 = 1
    | fact n = Int.* (n, fact (n-1))
end

signature MULT =
sig
  val mul : int * int -> int
end

structure Mult :> MULT =
struct
  fun mul (x, y) = x * y
end

structure FactFunStruct : FACT =
struct
  fun fact 0 = 1
    | fact n = Mult.mul (n, fact (n-1))
end


(* These three all seem to be within epsilon of each other. That is good. *)
structure FactMatchAcc : FACT =
struct
  fun fact' (m, 0) = m
    | fact' (m, n) = fact' (n*m, n-1)
  fun fact n = fact' (1, n)
end

structure FactMatchAccCurry : FACT =
struct
  fun fact' m 0 = m
    | fact' m n = fact' (n*m) (n-1)
  fun fact n = fact' 1 n
end

structure FactMatchAccCurry2 : FACT =
struct
  fun fact' m 0 = m
    | fact' m n = fact' (n*m) (n-1)
  val fact = fact' 1
end

(* A bunch more *)
structure FactUp : FACT =
struct
  fun fact n =
      let fun fact' m i =
              if i <= n then fact' (i*m) (i+1)
              else m
      in fact' 1 1 end
end

structure FactCond : FACT =
struct
  fun fact n =
      if n = 0
      then 1
      else n * fact (n-1)
end

structure FactCondAcc : FACT =
struct
  fun fact' m n =
      if n = 0
      then m
      else fact' (n*m) (n-1)
  val fact = fact' 1
end

structure FactCondAccNeq : FACT =
struct
  fun fact' m n =
      if n <> 0
      then fact' (n*m) (n-1)
      else m
  val fact = fact' 1
end

structure FactCondAccGreater : FACT =
struct
  fun fact' m n =
      if n > 0
      then fact' (n*m) (n-1)
      else m
  val fact = fact' 1
end


structure FactCps : FACT =
struct
  fun fact' k 0 = k 1
    | fact' k n = fact' (k o (fn m => n * m)) (n - 1)
  val fact = fact' (fn x => x)
end

structure FactIter : FACT =
struct
  fun for init next done =
      let fun loop x = if done x then x else loop (next x)
      in loop init end

  fun fact n =
      let val init = (0, 1)
          fun next   (i, m) = (i+1, m * (i+1))
          fun done   (i, _) = i = n
          fun result (_, m) = m
      in result (for init next done) end
end

structure FactIter2 : FACT =
struct
  fun for init next done =
      if done init then init else for (next init) next done

  fun fact n =
      let val init = (0, 1)
          fun next   (i, m) = (i+1, m * (i+1))
          fun done   (i, _) = i = n
          fun result (_, m) = m
      in result (for init next done) end
end

structure FactComb : FACT =
struct
  fun s f g x = f x (g x)
  fun k x y   = x
  fun b f g x = f (g x)
  fun c f g x = f x g
  fun y f x   = f (y f) x
  fun eq (x : int) y = x = y
  fun mul x y = x * y
  fun pred n = n - 1
  fun cond p f g x = if p x then f x else g x

  val fact =
      y (b (cond (eq 0) (k 1)) (b (s mul) (c b pred)))
end

structure FactImp : FACT =
struct
  fun fact n =
      let val ret = ref 1
          val i = ref n
          val () = 
              while !i > 0
              do (
                  ret := !ret * !i;
                  i := !i - 1)
      in !ret end
end

structure FactImp2 : FACT =
struct
  fun fact n =
      let val ret = ref 1
          val i = ref 1
          val () = 
              while !i <= n
              do (
                  ret := !ret * !i;
                  i := !i + 1)
      in !ret end
end

structure Tests =
struct
  fun add l x = l := x :: (!l)
  val names : string list ref = ref []
  val benchmarks : (int -> IntInf.int) list ref = ref []
end

functor TestFun (structure F : FACT val name : string) =
struct
  structure F = F
  val name = name
  val () = Tests.add Tests.names name

  val is = Int.toString
  fun id x = x

  fun time f x =
      let val start = Time.now ()
          val _ = f x
          val stop = Time.now ()
      in Time.toMicroseconds (Time.- (stop, start)) end

  fun test_speed m =
      let val () = if F.fact 5 <> 120 then print (name ^ ": anus!\n") else ()
          fun loop1 0 = ()
            | loop1 n = (F.fact m; loop1 (n-1))
          val iters = 10000000
          val _ = loop1 iters
      in time loop1 iters end
  val () = Tests.add Tests.benchmarks test_speed
end

structure T = TestFun(structure F = FactMatch val name = "match")
structure T = TestFun(structure F = FactFun val name = "fun")
structure T = TestFun(structure F = FactFun5 val name = "fun5")
structure T = TestFun(structure F = FactFunCurry val name = "fun_curry")
structure T = TestFun(structure F = FactFunInteger val name = "fun_int")
structure T = TestFun(structure F = FactFunInteger val name = "fun_struct")

structure T = TestFun(structure F = FactMatchAcc val name = "match_acc")
structure T = TestFun(structure F = FactMatchAccCurry val name = "match_curry")
structure T = TestFun(structure F = FactMatchAccCurry2
                      val name = "match_curry2")
structure T = TestFun(structure F = FactUp val name = "up")
structure T = TestFun(structure F = FactCond val name = "cond")
structure T = TestFun(structure F = FactCondAcc val name = "cond_acc")
structure T = TestFun(structure F = FactCondAccNeq val name = "cond_acc<>")
structure T = TestFun(structure F = FactCondAccGreater val name = "cond_acc<")
structure T = TestFun(structure F = FactCps val name = "cps")
structure T = TestFun(structure F = FactIter val name = "iter")
structure T = TestFun(structure F = FactIter2 val name = "iter2")
structure T = TestFun(structure F = FactComb val name = "comb")
structure T = TestFun(structure F = FactImp val name = "imp")
structure T = TestFun(structure F = FactImp2 val name = "imp2")

(* Replace the Tests structure with a less hacky one *)
structure TestsLol = Tests
structure Tests =
struct
  local
      fun fixup l = rev (!l)
  in
  val names = fixup Tests.names
  val benchmarks = fixup Tests.benchmarks
  end
end

(* Stolen from from SML/NJ lib because I was too
 * lazy to make a .mlb to import smlnj-lib to test with mlton *)
fun sort (op > : 'a * 'a -> bool) ls = let 
    fun merge([],ys) = ys
      | merge(xs,[]) = xs
      | merge(x::xs,y::ys) =
        if x > y then y::merge(x::xs,ys) else x::merge(xs,y::ys)
    fun mergepairs(ls as [l], k) = ls
      | mergepairs(l1::l2::ls,k) =
        if k mod 2 = 1 then l1::l2::ls
        else mergepairs(merge(l1,l2)::ls, k div 2)
      | mergepairs _ = raise Fail "ListSort.sort"
    fun nextrun(run,[])    = (rev run,[])
      | nextrun(run,x::xs) = if x > hd run then nextrun(x::run,xs)
                             else (rev run,x::xs)
    fun samsorting([], ls, k)    = hd(mergepairs(ls,0))
      | samsorting(x::xs, ls, k) = let 
            val (run,tail) = nextrun([x],xs)
        in samsorting(tail, mergepairs(run::ls,k+1), k+1)
        end
in 
    case ls of [] => [] | _ => samsorting(ls, [], 0)
end


(* Right pad a string to a certain length. Always add at least one space. *)
fun pad n s =
    let fun pad' n s = if String.size s >= n then s else pad' n (s^" ")
    in pad' (n-1) (s^" ") end

fun test n =
    let fun run f = f n
        val results = ListPair.zip (Tests.names, map run Tests.benchmarks)
        val results' = sort (fn ((_, x), (_, y)) => x > y) results
        fun print_test (name, time) =
            print (pad 14 name ^ LargeInt.toString time ^ "\n")
        val () = app print_test results'
    in () end

val fs = valOf o Int.fromString
fun main _ [n] = test (fs n)
  | main _ _ = ()

val _ = main (CommandLine.name ()) (CommandLine.arguments ())
