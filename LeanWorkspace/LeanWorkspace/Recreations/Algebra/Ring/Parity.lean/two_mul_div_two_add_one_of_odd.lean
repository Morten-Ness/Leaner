import Mathlib

variable {F α β : Type*}

variable {m n : ℕ}

theorem two_mul_div_two_add_one_of_odd (h : Odd n) : 2 * (n / 2) + 1 = n := by grind

