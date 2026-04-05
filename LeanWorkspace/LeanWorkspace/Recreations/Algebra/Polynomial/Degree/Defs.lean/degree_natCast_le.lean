import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem degree_natCast_le (n : ℕ) : Polynomial.degree (n : R[X]) ≤ 0 := degree_le_of_natDegree_le (by simp)

