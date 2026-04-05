import Mathlib

variable {K : Type*}

variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [CanonicallyOrderedAdd K]
  [Sub K] [OrderedSub K] {x y : K}

theorem geom_sum_of_one_lt (h : 1 < x) (n : ℕ) :
    ∑ i ∈ Finset.range n, x ^ i = (x ^ n - 1) / (x - 1) := eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom_sum_mul_of_one_le h.le n)

