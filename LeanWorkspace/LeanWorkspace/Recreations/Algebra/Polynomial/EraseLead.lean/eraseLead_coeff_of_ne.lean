import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem eraseLead_coeff_of_ne (i : ℕ) (hi : i ≠ f.natDegree) : f.eraseLead.coeff i = f.coeff i := by
  simp [Polynomial.eraseLead_coeff, hi]

