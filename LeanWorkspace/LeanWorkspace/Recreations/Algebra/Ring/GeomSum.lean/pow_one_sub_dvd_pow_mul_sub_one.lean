import Mathlib

variable {R S : Type*}

variable [Ring R] {x y : R}

theorem pow_one_sub_dvd_pow_mul_sub_one (x : R) (m n : ℕ) : x ^ m - 1 ∣ x ^ (m * n) - 1 := by
  rw [pow_mul]; exact sub_one_dvd_pow_sub_one (x ^ m) n

