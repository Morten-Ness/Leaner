import Mathlib

variable {α R S : Type*}

variable [Mul R] [Mul S]

theorem Prod.isRegular_mk {a : R} {b : S} : IsRegular (a, b) ↔ IsRegular a ∧ IsRegular b := by
  simp [isRegular_iff, and_and_and_comm]

