import Mathlib

variable {K : Type*} {v : K} {n : ℕ} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

theorem abs_sub_convergents_le' {b : K}
    (nth_partDen_eq : (of v).partDens.get? n = some b) :
    |v - (of v).convs n| ≤ 1 / (b * (of v).dens n * (of v).dens n) := by
  have not_terminatedAt_n : ¬(of v).TerminatedAt n := by
    simp [terminatedAt_iff_partDen_none, nth_partDen_eq]
  refine (GenContFract.abs_sub_convs_le not_terminatedAt_n).trans ?_
  -- One can show that `0 < (GenContFract.of v).dens n` but it's easier
  -- to consider the case `(GenContFract.of v).dens n = 0`.
  rcases (GenContFract.zero_le_of_den (K := K)).eq_or_lt' with
    ((hB : (GenContFract.of v).dens n = 0) | hB)
  · simp only [hB, mul_zero, zero_mul, div_zero, le_refl]
  · apply one_div_le_one_div_of_le
    · have : 0 < b := zero_lt_one.trans_le (GenContFract.of_one_le_get?_partDen nth_partDen_eq)
      apply_rules [mul_pos]
    · conv_rhs => rw [mul_comm]
      gcongr
      exact GenContFract.le_of_succ_get?_den nth_partDen_eq

