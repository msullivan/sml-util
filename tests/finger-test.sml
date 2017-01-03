structure JosephusTest =
struct
  infixr 5 << >< infix 5 >> open IdxSeq.Infix
  infixr 0 $ fun f $ x = f x

  structure S = IdxSeq
  (* From advent of code 2016 day 19 part 2 *)
  val num = 3005290

  fun makeSeq n = S.fromList (List.tabulate (n, fn i => i+1))
(*
  fun makeSeq n =
    let fun loop 0 s = s
          | loop n s = loop (n-1) (n << s)
    in loop n S.empty end
*)

  (*
  fun step s =
    let val (keep, s') = S.split 1 s
        val s'' = S.deleteAt ((S.length s' - 1) div 2) s'
    in s'' >< keep end
  *)
  fun step s =
    let val S.ConsV (keep, s') = S.viewl s
        val s'' = S.deleteAt ((S.length s' - 1) div 2) s'
    in s'' >> keep end

  fun until p f x = if p x then x else until p f (f x)
  fun solve n =
    S.nth 0 $ until (fn x => S.length x = 1) step $ makeSeq n

  fun run () = print (Int.toString (solve num) ^ "\n")

end;

JosephusTest.run ();
