import Mathlib

variable {m n : ℤ}

theorem even_coe_nat (n : ℕ) : Even (n : ℤ) ↔ Even n := by
  rw_mod_cast [Int.even_iff, Nat.even_iff]

