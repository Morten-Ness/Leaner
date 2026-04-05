import Mathlib

variable {F α β : Type*}

variable {m n : ℕ}

theorem two_dvd_mul_add_one (k : ℕ) : 2 ∣ k * (k + 1) := even_iff_two_dvd.mp (even_mul_succ_self k)

