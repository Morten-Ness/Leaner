import Mathlib

variable {R : Type*}

variable [Ring R]

theorem Splits.X_sub_C (a : R) : Polynomial.Splits (X - C a) := by
  simpa using Polynomial.Splits.X_add_C (-a)

