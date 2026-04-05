import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem eraseLead_X : Polynomial.eraseLead (Polynomial.X : R[X]) = 0 := Polynomial.eraseLead_monomial _ _

