import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem natDegree_mul_le {p q : R[X]} : Polynomial.natDegree (p * q) ≤ Polynomial.natDegree p + Polynomial.natDegree q := by
  apply natDegree_le_of_degree_le
  apply le_trans (Polynomial.degree_mul_le p q)
  rw [Nat.cast_add]
  apply add_le_add <;> apply Polynomial.degree_le_natDegree

