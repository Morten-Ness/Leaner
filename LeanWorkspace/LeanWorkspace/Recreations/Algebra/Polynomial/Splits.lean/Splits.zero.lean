import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem Splits.zero : Polynomial.Splits (0 : R[X]) := by
  simpa using Polynomial.Splits.C (0 : R)

