import Mathlib

variable {K : Type*} {v : K} {n : ℕ} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

theorem le_of_succ_get?_den {b : K}
    (nth_partDenom_eq : (of v).partDens.get? n = some b) :
    b * (of v).dens n ≤ (of v).dens (n + 1) := by
  rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux]
  exact GenContFract.le_of_succ_succ_get?_contsAux_b nth_partDenom_eq

