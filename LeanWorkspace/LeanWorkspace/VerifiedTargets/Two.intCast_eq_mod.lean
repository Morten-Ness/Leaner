import Mathlib

variable {R ι : Type*}

variable [Ring R] [CharP R 2]

theorem intCast_eq_mod (n : ℤ) : (n : R) = (n % 2 : ℤ) := by
  simp [CharTwo.intCast_eq_ite, Int.even_iff]

