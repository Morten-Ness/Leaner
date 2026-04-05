import Mathlib

variable {R : Type*} [Semiring R] (r : R) (f : R[X])

theorem taylor_eq_zero : Polynomial.taylor r f = 0 ↔ f = 0 := by
  rw [← leadingCoeff_eq_zero, ← leadingCoeff_eq_zero, Polynomial.leadingCoeff_taylor]

