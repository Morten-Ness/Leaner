import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem natDegree_add_le (p q : R[X]) : Polynomial.natDegree (p + q) ≤ max (Polynomial.natDegree p) (Polynomial.natDegree q) := by
  rcases le_max_iff.1 (Polynomial.degree_add_le p q) with h | h <;> simp [Polynomial.natDegree_le_natDegree h]

