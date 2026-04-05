import Mathlib

variable {R S : Type*}

variable [CommRing R]

theorem pow_sub_one_mul_geom_sum_eq_pow_sub_one_mul_geom_sum {x : R} {m n : ℕ} :
    (x ^ m - 1) * ∑ k ∈ range n, x ^ k = (x ^ n - 1) * ∑ k ∈ range m, x ^ k := by
  grind [geom_sum_mul]

