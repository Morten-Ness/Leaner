import Mathlib

variable {K : Type*}

variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [CanonicallyOrderedAdd K]
  [Sub K] [OrderedSub K] {x y : K}

theorem geom_sum_lt (h0 : x ≠ 0) (h1 : x < 1) (n : ℕ) : ∑ i ∈ range n, x ^ i < (1 - x)⁻¹ := by
  rw [← pos_iff_ne_zero] at h0
  rw [geom_sum_of_lt_one h1, div_lt_iff₀, inv_mul_cancel₀, tsub_lt_self_iff]
  · exact ⟨h0.trans h1, pow_pos h0 n⟩
  · rwa [ne_eq, tsub_eq_zero_iff_le, not_le]
  · rwa [tsub_pos_iff_lt]

