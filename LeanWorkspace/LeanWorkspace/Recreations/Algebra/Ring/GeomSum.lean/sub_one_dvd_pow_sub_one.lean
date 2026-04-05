import Mathlib

variable {R S : Type*}

variable [Ring R] {x y : R}

theorem sub_one_dvd_pow_sub_one (x : R) (n : ℕ) : x - 1 ∣ x ^ n - 1 := by
  conv_rhs => rw [← one_pow n]
  exact (Commute.one_right x).sub_dvd_pow_sub_pow n

