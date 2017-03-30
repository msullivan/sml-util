signature SET_CORE =
sig
  type 'a set
  val compare : ('a * 'b -> order) -> 'a set * 'b set -> order
end
