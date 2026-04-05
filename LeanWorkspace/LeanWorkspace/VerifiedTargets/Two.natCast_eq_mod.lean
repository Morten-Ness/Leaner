import Mathlib

variable {R ι : Type*}

variable [AddMonoidWithOne R]

variable [CharP R 2]

theorem natCast_eq_mod (n : ℕ) : (n : R) = (n % 2 : ℕ) := by
  simp [CharTwo.natCast_eq_ite, Nat.even_iff]

