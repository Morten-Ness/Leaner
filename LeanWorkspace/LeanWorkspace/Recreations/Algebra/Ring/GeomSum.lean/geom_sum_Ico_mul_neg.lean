import Mathlib

variable {R S : Type*}

variable [Ring R] {x y : R}

theorem geom_sum_Ico_mul_neg (x : R) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i ∈ Finset.Ico m n, x ^ i) * (1 - x) = x ^ m - x ^ n := by
  rw [sum_Ico_eq_sub _ hmn, sub_mul, geom_sum_mul_neg, geom_sum_mul_neg, sub_sub_sub_cancel_left]

