import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem degree_X_le : Polynomial.degree (Polynomial.X : R[X]) ≤ 1 := Polynomial.degree_monomial_le _ _

