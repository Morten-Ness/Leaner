import Mathlib

variable {R S : Type*}

variable [Ring R] {x y : R}

theorem geom_sum_Ico_mul (x : R) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i ∈ Finset.Ico m n, x ^ i) * (x - 1) = x ^ n - x ^ m := by
  rw [sum_Ico_eq_sub _ hmn, sub_mul, geom_sum_mul, geom_sum_mul, sub_sub_sub_cancel_right]

