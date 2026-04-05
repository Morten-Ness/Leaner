import Mathlib

variable {R S : Type*}

variable [Ring R] {x y : R}

theorem one_sub_dvd_one_sub_pow (x : R) (n : ℕ) : 1 - x ∣ 1 - x ^ n := by
  conv_rhs => rw [← one_pow n]
  exact (Commute.one_left x).sub_dvd_pow_sub_pow n

