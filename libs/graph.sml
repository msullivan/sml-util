(* Some simple operations over maps of sets *)
functor SetMap(structure Set : GOOD_SET structure Map : GOOD_MAP) =
struct
  structure M = Map
  structure S = Set

  type set_map = S.set M.map
  val empty = M.empty

  fun get_entries graph o1 = getOpt (M.find (graph, o1), S.empty)
  fun add_empty graph o1 =
      if M.inDomain (graph, o1) then graph else M.insert (graph, o1, S.empty)
  fun add_entry graph o1 o2 =
      M.insert (graph, o1, S.add (get_entries graph o1, o2))
  fun remove_entry graph o1 o2 =
      M.insert (graph, o1, S.delete (get_entries graph o1, o2))
      handle NotFound => graph
  fun has_entry graph o1 o2 =
      S.has (get_entries graph o1) o2
  fun add_many_entries graph o1 o2s =
      M.insert (graph, o1, S.union (get_entries graph o1, o2s))
end


(* A bunch of graph operations. This isn't really an abstract
   data structure, since the type representation is not hidden
   and there isn't a signature or anything. It's just a collection
   of functions for dealing with the interference graph. *)
functor Graph (Set : GOOD_SET) =
struct
  structure S = Set
  structure M = S.Map

  structure SM = SetMap(structure Set = S structure Map = M)

  type graph = SM.set_map
  val empty = SM.empty
  val get_edges = SM.get_entries
  val add_node = SM.add_empty
  val add_edge1 = SM.add_entry
  val remove_edge1 = SM.remove_entry
  val has_edge = SM.has_entry
  val add_many_edges = SM.add_many_entries

  fun add_edge graph o1 o2 = add_edge1 (add_edge1 graph o1 o2) o2 o1
  fun remove_edge graph o1 o2 = remove_edge1 (remove_edge1 graph o1 o2) o2 o1

  fun remove_node graph o1 =
      let val (graph', neighbors) = M.remove (graph, o1)
      in S.foldl (fn (o2, g) => remove_edge g o2 o1) graph' neighbors end

  (* Fix up the graph by making sure we have all double edges. *)
  fun normalize_graph graph =
      M.foldli (fn (o1, o2s, graph) =>
                  S.foldl (fn (o2, graph) => add_edge1 graph o2 o1) graph o2s)
      graph graph

  (* Generate a graph by reversing all of the edges of an existing graph. *)
  fun reverse_graph graph =
      M.foldli
      (fn (u, edges, graph) => S.foldl
                        (fn (v, graph) => add_edge1 graph v u)
                        graph edges)
      M.empty graph

  (* Generate a traversal ordering starting from a given start node.
   * The is_postorder argument specifies the kind of ordering.
   * Also return the set of reachable nodes from this start. *)
  fun general_dfs is_postorder graph start =
      let fun ordering (n, (order, seen)) =
              if S.has seen n then (order, seen) else
              let val seen' = S.ins seen n
                  val order = if is_postorder then order else n::order
                  val (order', seen'') = S.foldl ordering (order, seen') (get_edges graph n)
                  val order' = if is_postorder then n::order' else order'
              in (order', seen'') end
          val (rorder, seen) = ordering (start, ([], S.empty))
      in (rev rorder, seen) end

  fun generate_ordering x y = Util.first o general_dfs x y
  fun find_reachable x = Util.second o general_dfs true x

  val generate_postorder = generate_ordering true
  val generate_preorder = generate_ordering false

  fun listify s = M.listItemsi (M.map S.listItems s)

  fun format fmt graph = M.format fmt (S.format fmt) graph

  (* Compute the transitive closure of a graph. This isn't particularly efficient
   * and I know for a fact we could do better in the cases we need it, but this is
   * *really* easy. I'll do something better if we have perf problems. *)
  fun transitive_closure graph =
      M.mapi (fn (n,_) => find_reachable graph n) graph
end

structure OperGraph = Graph(OperSet)
structure IntGraph = Graph(IntSet)
