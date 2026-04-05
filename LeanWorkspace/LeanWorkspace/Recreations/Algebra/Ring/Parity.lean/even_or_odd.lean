import Mathlib

variable {F α β : Type*}

variable {m n : ℕ}

theorem even_or_odd (n : ℕ) : Even n ∨ Odd n := (Nat.even_xor_odd n).or

