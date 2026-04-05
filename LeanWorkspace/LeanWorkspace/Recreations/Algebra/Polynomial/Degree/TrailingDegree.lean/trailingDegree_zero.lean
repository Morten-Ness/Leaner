import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem trailingDegree_zero : Polynomial.trailingDegree (0 : R[X]) = ⊤ := rfl

