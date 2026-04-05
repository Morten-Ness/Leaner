import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem eraseLead_support (f : R[X]) : f.eraseLead.support = f.support.erase f.natDegree := by
  simp only [Polynomial.eraseLead, support_erase]

