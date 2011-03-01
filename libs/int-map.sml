(* Patricia trie based maps on keys that can be mapped to integers.
 * Fleshed out into a full ORD_MAP implementation by
 * Michael Sullivan <sully@msully.net>.
 *
 * Based on source code adapted from
 *   Okasaki & Gill, "Fast Mergeable Integer Maps", ML Workshop '98
 * Also takes code for certain generic operations from smlnj-lib splay map.
 *)

(***********************************************************************)

signature WORDABLE =
sig
  type wordable_key
  val wordify : wordable_key -> word
end

functor WordMapFn(Wordable : WORDABLE) : ORD_MAP =
struct
  val wordify = Wordable.wordify

  structure Key =
  struct
    type ord_key = Wordable.wordable_key
    fun compare (x, y) = Word.compare (wordify x, wordify y)
  end

  structure W = Word

  (* Finding the highest set bit is a fairly expensive part of insert,
   * so I spent a bunch of time trying to tune it. On my machine running
   * SML/NJ v110.72, it seems that we perform best with the original looping
   * code (even when the other alternatives modify the rest of the map to not
   * pass around a guess for branchingBit.
   * This is in spite of the fact that on pure bit checking tests, the loop version
   * performs quite a bit slower. *)
  fun highestBitLoop (x,m) =
      let val x' = W.andb (x,W.notb (m-0w1))
          fun highb (x,m) =
              if x=m then m else highb (W.andb (x,W.notb m),m+m)
      in highb (x',m) end
  fun highestBitTwiddle (x, _) =
      let val x = W.orb (x, W.>>(x, 0wx1))
          val x = W.orb (x, W.>>(x, 0wx2))
          val x = W.orb (x, W.>>(x, 0wx4))
          val x = W.orb (x, W.>>(x, 0wx8))
          val x = W.orb (x, W.>>(x, 0wx10))
      in W.xorb (x, W.>>(x, 0wx1)) end
  structure V = (*Unsafe.*)Vector
  val table = Vector.tabulate (65336, (fn x => highestBitTwiddle (x, 0w1)) o W.fromInt)
  fun highestBitLookup (x, _) =
      if x < 0w65336 then
          V.sub (table, W.toInt x)
      else W.<<(V.sub (table, W.toInt (W.>>(x,0w16))), 0w16)

  val highestBit = highestBitLoop

  fun branchingBit (m,p0,p1) = highestBit (W.xorb (p0,p1), m)
  fun mask (k,m) = W.orb (k,m-0w1+m) - m
  fun matchPrefix (k,p,m) = (mask (k,m) = p)
  fun swap (k,x,y) = (k,y,x)

  datatype 'a Dict =
      Empty
    | Lf of word * Key.ord_key * 'a
    | Br of word * word * 'a Dict * 'a Dict
  type 'a map = 'a Dict

  fun br (_,_,Empty,t) = t
    | br (_,_,t,Empty) = t
    | br (p,m,t0,t1) = Br (p,m,t0,t1)

  (* 
   * Lf (k,rk,x):
   *   k is the "wordified" key, rk is the "real" key
   * Br (p,m,t0,t1):
   *   p is the largest common prefix for all the keys in this tree
   *   m is the branching bit
   *     (m is a power of 2, only the bits above m are valid in p)
   *   t0 contains all the keys with a 0 in the branching bit
   *   t1 contains all the keys with a 1 in the branching bit
   *)

  val empty = Empty
  fun isEmpty Empty = true
    | isEmpty _ = false
  fun singleton (k,x) = Lf (wordify k,k,x)

  fun find (t,k) =
      let val w = wordify k
          fun look Empty = NONE
            | look (Lf (j,_,x)) = if j=w then SOME x else NONE
            | look (Br (p,_,t0,t1)) =
              if w <= p then look t0
              else look t1
      in look t end

  fun join (m,p0,t0,p1,t1) =
      (* combine two trees with prefixes p0 and p1,
       * where p0 and p1 are known to disagree
       *)
      let val m = branchingBit (m,p0,p1)
      in if p0 < p1 then Br (mask (p0,m), m, t0, t1)
         else Br (mask (p0,m), m, t1, t0)
      end

  (* Code duplicated without the selector function for minor performance win.
   * Sigh. *)
  fun insertw (t,w,rk,x) =
      let fun ins Empty = Lf (w,rk,x)
            | ins (t as Lf (j,_,_)) =
              if j=w then Lf (w, rk, x)
              else join (0w1,w,Lf (w,rk,x),j,t)
            | ins (t as Br (p,m,t0,t1)) =
              if matchPrefix (w,p,m) then
                  if w <= p then Br (p,m,ins t0,t1)
                  else Br (p,m,t0,ins t1)
              else join (m+m,w,Lf (w,rk,x),p,t)
      in ins t end
  fun insertWith c (t,w,rk,x) =
      let fun ins Empty = Lf (w,rk,x)
            | ins (t as Lf (j,_,y)) =
              if j=w then Lf (w, rk, c (rk, x, y))
              else join (0w1,w,Lf (w,rk,x),j,t)
            | ins (t as Br (p,m,t0,t1)) =
              if matchPrefix (w,p,m) then
                  if w <= p then Br (p,m,ins t0,t1)
                  else Br (p,m,t0,ins t1)
              else join (m+m,w,Lf (w,rk,x),p,t)
      in ins t end

  fun remove (m, k) =
      let val w = wordify k
          fun del Empty = raise LibBase.NotFound
            | del (Lf (j,_,x)) = if j=w then (Empty, x) else raise LibBase.NotFound
            | del (Br (p,m,t0,t1)) =
              if w <= p then let val (t, x) = del t0 in (br (p, m, t, t1), x) end
              else let val (t, x) = del t1 in (br (p, m, t0, t), x) end
      in del m end

  fun insert (t,k,x) = insertw (t,wordify k,k,x)
  fun insert' ((k,x),t) = insertw (t,wordify k,k,x)
  fun lookup (m, k) = case find (m, k) of SOME v => v
                                        | NONE => raise LibBase.NotFound
  fun inDomain (m, k) = isSome (find (m, k))

  fun unionWithi c (s,t) =
      let fun mrg (s as Br (p,m,s0,s1), t as Br (q,n,t0,t1)) =
              if m<n then
                  if matchPrefix (p,q,n) then
                      if p <= q then Br (q,n,mrg (s,t0),t1)
                      else Br (q,n,t0,mrg (s,t1))
                  else join (n+n,p,s,q,t)
              else if m>n then
                  if matchPrefix (q,p,m) then
                      if q <= p then Br (p,m,mrg (s0,t),s1)
                      else Br (p,m,s0,mrg (s1,t))
                  else join (m+m,p,s,q,t)
              else (* if m=n then *)
                  if p=q then Br (p,m,mrg (s0,t0),mrg (s1,t1))
                  else join (m+m,p,s,q,t)
            | mrg (t as Br _, Lf (w,rk,x)) = insertWith (c o swap) (t,w,rk,x)
            | mrg (t as Br _, Empty) = t
            | mrg (Lf (w,rk,x), t) = insertWith c (t,w,rk,x)
            | mrg (Empty, t) = t
      in mrg (s,t) end
  fun unionWith c (s,t) = unionWithi (fn (_,x,y) => c (x,y)) (s,t)

  fun firsti m =
      let fun f Empty = NONE
            | f (Lf (_, rk, x)) = SOME (rk, x)
            | f (Br (_, _, l, _)) = f l
      in f m end
  fun first m = Option.map (fn (_,x)=>x) (firsti m)

  fun numItems Empty = 0
    | numItems (Lf _) = 1
    | numItems (Br (_, _, l, r)) = numItems l + numItems r

  fun appi g m =
      let fun f Empty = ()
            | f (Lf (_, rk, x)) = g (rk, x)
            | f (Br (_, _, l, r)) = (f l; f r)
      in f m end
  fun app f m = appi (fn (_,x)=>f x) m

  fun mapi g m =
      let fun f Empty = Empty
            | f (Lf (k, rk, x)) = Lf (k, rk, g (rk, x))
            | f (Br (p, m, l, r)) = Br (p, m, f l, f r)
      in f m end
  fun map f m = mapi (fn (_,x)=>f x) m

  fun mapPartiali g m =
      let fun f Empty = Empty
            | f (Lf (k, rk, x)) =
              (case g (rk, x) of
                   NONE => Empty
                 | SOME x' => Lf (k, rk, x'))
            | f (Br (p, m, l, r)) = br (p, m, f l, f r)
      in f m end
  fun mapPartial f m = mapPartiali (fn (_,x)=>f x) m

  fun filteri predFn m =
      let fun f Empty = Empty
            | f (n as (Lf (_, rk, x))) =
              if predFn (rk, x) then n else Empty
            | f (Br (p, m, l, r)) = br (p, m, f l, f r)
      in f m end
  fun filter f m = filteri (fn (_,x)=>f x) m

  fun foldli g z m =
      let fun f (Empty, z) = z
            | f (Lf (_, rk, x), z) = g (rk, x, z)
            | f (Br (_, _, l, r), z) = f (r, f (l, z))
      in f (m, z) end
  fun foldl f m = foldli (fn (_,x,z)=>f (x,z)) m

  fun foldri g z m =
      let fun f (Empty, z) = z
            | f (Lf (_, rk, x), z) = g (rk, x, z)
            | f (Br (_, _, l, r), z) = f (l, f (r, z))
      in f (m, z) end
  fun foldr f m = foldri (fn (_,x,z)=>f (x,z)) m


  fun listItemsi m = foldli (fn (k,x,l) => (k,x)::l) nil m
  fun listKeys m = foldli (fn (k,_,l) => k::l) nil m
  fun listItems m = foldl (op ::) nil m

  (* FIXME: This is an atrocious implementation of collate. It is linear in the best
   * case instead of in just the worst case. *)
  fun collate f (m1, m2) = List.collate f (listItems m1, listItems m2)

  (* the following are generic implementations of the intersectWith
   * and mergeWith operetions.  These should be specialized for the internal
   * representations at some point.
   *)
  fun intersectWith f (m1, m2) = let
      (* iterate over the elements of m1, checking for membership in m2 *)
      fun intersect f (m1, m2) = let
	  fun ins (key, x, m) = (case find(m2, key)
		                  of NONE => m
			           | (SOME x') => insert(m, key, f(x, x'))
		                (* end case *))
      in
	  foldli ins empty m1
      end
  in
      if (numItems m1 > numItems m2)
      then intersect f (m1, m2)
      else intersect (fn (a, b) => f(b, a)) (m2, m1)
  end

  fun intersectWithi f (m1, m2) = let
      (* iterate over the elements of m1, checking for membership in m2 *)
      fun intersect f (m1, m2) = let
	  fun ins (key, x, m) = (case find(m2, key)
		                  of NONE => m
			           | (SOME x') => insert(m, key, f(key, x, x'))
		                (* end case *))
      in
	  foldli ins empty m1
      end
  in
      if (numItems m1 > numItems m2)
      then intersect f (m1, m2)
      else intersect (fn (k, a, b) => f(k, b, a)) (m2, m1)
  end

  fun mergeWith f (m1, m2) = let
      fun merge ([], [], m) = m
	| merge ((k1, x1)::r1, [], m) = mergef (k1, SOME x1, NONE, r1, [], m)
        | merge ([], (k2, x2)::r2, m) = mergef (k2, NONE, SOME x2, [], r2, m)
	| merge (m1 as ((k1, x1)::r1), m2 as ((k2, x2)::r2), m) = (
	  case Key.compare (k1, k2)
	   of LESS => mergef (k1, SOME x1, NONE, r1, m2, m)
	    | EQUAL => mergef (k1, SOME x1, SOME x2, r1, r2, m)
	    | GREATER => mergef (k2, NONE, SOME x2, m1, r2, m)
	  (* end case *))
      and mergef (k, x1, x2, r1, r2, m) = (case f (x1, x2)
		                            of NONE => merge (r1, r2, m)
		                             | SOME y => merge (r1, r2, insert(m, k, y))
		                          (* end case *))
  in
      merge (listItemsi m1, listItemsi m2, empty)
  end

  fun mergeWithi f (m1, m2) = let
      fun merge ([], [], m) = m
	| merge ((k1, x1)::r1, [], m) = mergef (k1, SOME x1, NONE, r1, [], m)
	| merge ([], (k2, x2)::r2, m) = mergef (k2, NONE, SOME x2, [], r2, m)
        | merge (m1 as ((k1, x1)::r1), m2 as ((k2, x2)::r2), m) = (
	  case Key.compare (k1, k2)
	   of LESS => mergef (k1, SOME x1, NONE, r1, m2, m)
	    | EQUAL => mergef (k1, SOME x1, SOME x2, r1, r2, m)
	    | GREATER => mergef (k2, NONE, SOME x2, m1, r2, m)
	  (* end case *))
      and mergef (k, x1, x2, r1, r2, m) = (case f (k, x1, x2)
		                            of NONE => merge (r1, r2, m)
		                             | SOME y => merge (r1, r2, insert(m, k, y))
		                          (* end case *))
  in
      merge (listItemsi m1, listItemsi m2, empty)
  end
end

structure WordWordable : WORDABLE =
struct
  type wordable_key = word
  fun wordify x = x
end

structure IntWordable =
struct
  type wordable_key = int
  val imax = 
      case Int.maxInt of
          NONE => 0w0 (* I have no idea! Fuck! *)
        | SOME w =>(Word.fromInt w)+0w1 (* 0wx40000000 in sml/nj... *)
  fun wordify x = Word.fromInt x + imax
end

(* Then you can do... *)
structure WordMap = WordMapFn(WordWordable)
structure IntMap = WordMapFn(IntWordable)
