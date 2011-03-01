(* Some utility functions for formatting output. *)

structure Print =
struct
  fun say s = TextIO.output (TextIO.stdOut, s ^ "\n")
  fun esay s = TextIO.output (TextIO.stdErr, s ^ "\n")
  fun tsay s = say (Time.toString (Time.now ()) ^ ": " ^ s)

  val is = Int.toString

  fun fmt_int n = if n > 0 then is n else "-" ^ is (~n)
  fun fmt_list' s f l = (String.concatWith s (map f l))
  fun fmt_list f l = "[" ^ (fmt_list' ", " f l) ^ "]"

  fun fmt_tup2 f g (a, b) = "("^(f a)^", "^(g b)^")"
  fun fmt_tup3 f g h (a, b, c) = "("^(f a)^", "^(g b)^","^(h c)^")"

  (* Right pad a string to a certain length. Always add at least one space. *)
  fun pad n s =
      let fun pad' n s = if String.size s >= n then s else pad' n (s^" ")
      in pad' (n-1) (s^" ") end

  val indent_amt = "    "
  fun indent n = String.concat (List.tabulate (n, fn _ => indent_amt))
end
