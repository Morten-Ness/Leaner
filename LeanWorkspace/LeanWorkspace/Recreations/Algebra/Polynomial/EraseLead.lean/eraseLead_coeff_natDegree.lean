import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem eraseLead_coeff_natDegree : f.eraseLead.coeff f.natDegree = 0 := by simp [Polynomial.eraseLead_coeff]

