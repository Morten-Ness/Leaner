import Mathlib

variable {m n : ℕ}

theorem two_not_dvd_two_mul_sub_one {n} : 0 < n → ¬2 ∣ 2 * n - 1 := by lia

