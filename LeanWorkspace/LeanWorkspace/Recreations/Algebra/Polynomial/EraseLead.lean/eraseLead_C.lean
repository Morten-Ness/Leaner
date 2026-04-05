import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem eraseLead_C (r : R) : Polynomial.eraseLead (Polynomial.C r) = 0 := Polynomial.eraseLead_monomial _ _

