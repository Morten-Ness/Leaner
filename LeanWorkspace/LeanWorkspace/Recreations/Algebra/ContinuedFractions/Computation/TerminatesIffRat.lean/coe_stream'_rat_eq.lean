import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

variable {v : K} {q : ℚ}

theorem coe_stream'_rat_eq (v_eq_q : v = (↑q : K)) :
    ((GenContFract.IntFractPair.stream q).map (Option.map (mapFr (↑))) : Stream' <| Option <| GenContFract.IntFractPair K) =
      GenContFract.IntFractPair.stream v := by
  funext n; exact GenContFract.IntFractPair.coe_stream_nth_rat_eq v_eq_q n

