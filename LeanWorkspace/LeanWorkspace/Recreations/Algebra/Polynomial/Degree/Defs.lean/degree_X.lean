import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [Nontrivial R] {p q : R[X]}

theorem degree_X : Polynomial.degree (Polynomial.X : R[X]) = 1 := Polynomial.degree_monomial _ one_ne_zero

