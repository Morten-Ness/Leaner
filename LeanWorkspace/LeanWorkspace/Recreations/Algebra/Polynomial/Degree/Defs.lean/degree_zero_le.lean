import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem degree_zero_le : Polynomial.degree (0 : R[X]) ≤ 0 := Polynomial.natDegree_eq_zero_iff_degree_le_zero.mp rfl

