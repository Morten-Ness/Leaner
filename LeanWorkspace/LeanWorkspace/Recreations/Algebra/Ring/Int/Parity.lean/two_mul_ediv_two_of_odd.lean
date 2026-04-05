import Mathlib

variable {m n : ℤ}

theorem two_mul_ediv_two_of_odd (h : Odd n) : 2 * (n / 2) = n - 1 := by grind

