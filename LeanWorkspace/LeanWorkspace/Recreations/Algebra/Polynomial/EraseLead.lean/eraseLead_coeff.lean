import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem eraseLead_coeff (i : ℕ) :
    f.eraseLead.coeff i = if i = f.natDegree then 0 else f.coeff i := by
  simp only [Polynomial.eraseLead, coeff_erase]

