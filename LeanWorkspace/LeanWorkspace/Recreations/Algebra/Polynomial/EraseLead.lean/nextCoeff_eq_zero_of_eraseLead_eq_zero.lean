import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem nextCoeff_eq_zero_of_eraseLead_eq_zero (h : f.eraseLead = 0) : f.nextCoeff = 0 := by
  by_contra h₂
  exact leadingCoeff_ne_zero.mp (Polynomial.leadingCoeff_eraseLead_eq_nextCoeff h₂ ▸ h₂) h

