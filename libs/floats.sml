structure FloatFmt =
struct
  (* Get integral exponent and mantissa.
   * r = man * 2^exp *)
  fun toIntExpMan r =
      let val {exp, man} = Real.toManExp r
          val manScaled = Real.fromManExp {exp=Real.precision, man=man}
          val manInt = Real.toLargeInt IEEEReal.TO_NEAREST manScaled
      in {exp=exp-Real.precision, man=manInt} end


  fun fromIntExpMan {exp, man} =
      Real.fromManExp {man=1.0, exp=exp} * Real.fromLargeInt man


end
