import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

variable {v : K} {q : ℚ}

theorem coe_of_h_rat_eq (v_eq_q : v = (↑q : K)) : (↑((of q).h : ℚ) : K) = (of v).h := by
  simp_all

