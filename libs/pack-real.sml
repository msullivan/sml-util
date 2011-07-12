(* SML has optional structures in the basis called PackRealLittle and
 * PackRealBig (implementing the PACK_REAL signature) for marshalling and
 * unmarshalling real data. While mlton provides these, SML/NJ does not.
 * This is an implementation of PACK_REAL for SML/NJ built on top of 
 * unsafe casting and subscripting. *)

local
functor PackRealFn(val isBigEndian : bool) : PACK_REAL =
struct
  type real = real
  val bytesPerElem = 8
  val isBigEndian = isBigEndian

  structure UR = Unsafe.Real64Array
  structure UB = Unsafe.Word8Array
  structure A = Word8Array
  structure AS = Word8ArraySlice
  structure V = Word8Vector
  structure VS = Word8VectorSlice

  fun rawToBytes x =
      let val a : UR.array = Unsafe.cast (RealArray.array (1, x))
      in V.tabulate (bytesPerElem, fn i => UB.sub (a, i)) end

  fun rawFromBytes (v : V.vector) = UR.sub (Unsafe.cast v, 0)

  (* Compare against a known result to determine the system's endianness
   * and swap around byte orders if it differs from our intended endianness. *)
  val isSystemBigEndian = V.sub (rawToBytes 3.14159265358979323, 0) <> 0wx18
  val swizzle = if isBigEndian = isSystemBigEndian then (fn v => v) else
                (fn v => V.tabulate (bytesPerElem, fn i => V.sub (v, bytesPerElem-i-1)))

  val toBytes = swizzle o rawToBytes
  val fromBytes = rawFromBytes o swizzle

  fun subVec (v, i) = 
      fromBytes (VS.vector (VS.slice (v, bytesPerElem*i, SOME bytesPerElem)))
  fun subArr (v, i) = 
      fromBytes (AS.vector (AS.slice (v, bytesPerElem*i, SOME bytesPerElem)))
  fun update (v, i, x) = A.copyVec { src = toBytes x, dst = v, di = i*bytesPerElem }
end

in
structure PackRealLittle = PackRealFn(val isBigEndian = false)
structure PackReal64Little = PackRealLittle
structure PackRealBig = PackRealFn(val isBigEndian = true)
structure PackReal64Big = PackRealBig
end
