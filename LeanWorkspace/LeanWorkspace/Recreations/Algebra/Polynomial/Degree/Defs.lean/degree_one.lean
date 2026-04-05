import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [Nontrivial R] {p q : R[X]}

theorem degree_one : Polynomial.degree (1 : R[X]) = (0 : WithBot ℕ) := Polynomial.degree_C one_ne_zero

