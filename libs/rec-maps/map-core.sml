signature MAP_CORE =
sig
  type ('k, 'v) map
  val collate : ('a * 'b -> order) -> ('c * 'd -> order) ->
                ('a, 'c) map * ('b, 'd) map -> order
end
