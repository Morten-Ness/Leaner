import Mathlib

variable {F α β : Type*}

variable {m n : ℕ}

theorem Odd.of_mul_left (h : Odd (m * n)) : Odd m := (Nat.odd_mul.mp h).1

