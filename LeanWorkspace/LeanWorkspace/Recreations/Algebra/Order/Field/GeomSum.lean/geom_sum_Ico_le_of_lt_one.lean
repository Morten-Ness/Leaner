import Mathlib

variable {K : Type*}

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] {x : K} {m n : ℕ}

theorem geom_sum_Ico_le_of_lt_one (hx : 0 ≤ x) (h'x : x < 1) :
    ∑ i ∈ Ico m n, x ^ i ≤ x ^ m / (1 - x) := by
  rcases le_or_gt m n with (hmn | hmn)
  · rw [geom_sum_Ico' h'x.ne hmn]
    apply div_le_div₀ (pow_nonneg hx _) _ (sub_pos.2 h'x) le_rfl
    simpa using pow_nonneg hx _
  · rw [Ico_eq_empty, sum_empty]
    · apply div_nonneg (pow_nonneg hx _)
      simpa using h'x.le
    · simpa using hmn.le

