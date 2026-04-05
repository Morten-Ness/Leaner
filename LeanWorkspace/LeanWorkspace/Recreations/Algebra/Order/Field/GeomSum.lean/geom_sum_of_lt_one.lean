import Mathlib

variable {K : Type*}

variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [CanonicallyOrderedAdd K]
  [Sub K] [OrderedSub K] {x y : K}

theorem geom_sum_of_lt_one (h : x < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, x ^ i = (1 - x ^ n) / (1 - x) := eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom_sum_mul_of_le_one h.le n)

