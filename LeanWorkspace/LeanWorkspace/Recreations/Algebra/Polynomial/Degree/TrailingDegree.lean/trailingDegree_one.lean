import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] [Nontrivial R] {p q : R[X]}

theorem trailingDegree_one : Polynomial.trailingDegree (1 : R[X]) = (0 : ℕ∞) := Polynomial.trailingDegree_C one_ne_zero

