import Mathlib

variable {m n : ℤ}

theorem two_dvd_mul_add_one (k : ℤ) : 2 ∣ k * (k + 1) := even_iff_two_dvd.mp (Int.even_mul_succ_self k)

