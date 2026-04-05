import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem Splits.X : Polynomial.Splits (X : R[X]) := by
  simpa using Polynomial.Splits.X_add_C (0 : R)

