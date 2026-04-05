import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem coeff_zero_reverse (f : R[X]) : coeff (Polynomial.reverse f) 0 = leadingCoeff f := by
  rw [Polynomial.coeff_reverse, Polynomial.revAt_le (zero_le f.natDegree), tsub_zero, leadingCoeff]

