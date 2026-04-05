import Mathlib

variable {K : Type*}

variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [CanonicallyOrderedAdd K]
  [Sub K] [OrderedSub K] {x y : K}

theorem geom₂_sum_of_lt (h : x < y) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = (y ^ n - x ^ n) / (y - x) := eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom_sum₂_mul_of_le h.le n)

