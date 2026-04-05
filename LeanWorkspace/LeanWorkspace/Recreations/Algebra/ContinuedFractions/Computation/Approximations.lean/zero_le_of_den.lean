import Mathlib

variable {K : Type*} {v : K} {n : ℕ} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

theorem zero_le_of_den : 0 ≤ (of v).dens n := by
  rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux]; exact GenContFract.zero_le_of_contsAux_b

