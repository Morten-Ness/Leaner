import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem eraseLead_zero : Polynomial.eraseLead (0 : R[X]) = 0 := by simp only [Polynomial.eraseLead, erase_zero]

