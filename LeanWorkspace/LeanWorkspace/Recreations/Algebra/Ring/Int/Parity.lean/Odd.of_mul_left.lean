import Mathlib

variable {m n : ℤ}

theorem Odd.of_mul_left (h : Odd (m * n)) : Odd m := (Int.odd_mul.mp h).1

