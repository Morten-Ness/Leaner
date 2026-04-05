import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

variable {v : K} {q : ℚ}

theorem coe_of_rat_eq (v_eq_q : v = (↑q : K)) :
    ((GenContFract.IntFractPair.of q).mapFr (↑) : GenContFract.IntFractPair K) = GenContFract.IntFractPair.of v := by
  simp [GenContFract.IntFractPair.of, v_eq_q]

