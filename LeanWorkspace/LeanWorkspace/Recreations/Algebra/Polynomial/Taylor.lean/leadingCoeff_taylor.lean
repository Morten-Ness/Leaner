import Mathlib

variable {R : Type*} [Semiring R] (r : R) (f : R[X])

theorem leadingCoeff_taylor : (Polynomial.taylor r f).leadingCoeff = f.leadingCoeff := by
  rw [leadingCoeff, leadingCoeff, Polynomial.natDegree_taylor, Polynomial.coeff_taylor_natDegree, leadingCoeff]

