import Mathlib

variable {K : Type*}

variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [CanonicallyOrderedAdd K]
  [Sub K] [OrderedSub K] {x y : K}

theorem geom₂_sum_of_gt (h : y < x) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = (x ^ n - y ^ n) / (x - y) := eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom_sum₂_mul_of_ge h.le n)

