import Mathlib

variable {F α β : Type*}

variable {m n : ℕ}

theorem Odd.of_mul_right (h : Odd (m * n)) : Odd n := (Nat.odd_mul.mp h).2

