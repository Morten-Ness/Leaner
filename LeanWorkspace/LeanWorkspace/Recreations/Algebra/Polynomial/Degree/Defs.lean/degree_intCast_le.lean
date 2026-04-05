import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R]

theorem degree_intCast_le (n : ℤ) : Polynomial.degree (n : R[X]) ≤ 0 := degree_le_of_natDegree_le (by simp)

