import Mathlib

variable {m n : ℤ}

theorem Odd.of_mul_right (h : Odd (m * n)) : Odd n := (Int.odd_mul.mp h).2

