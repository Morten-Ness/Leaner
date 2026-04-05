import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem degree_eq_iff_natDegree_eq_of_pos {p : R[X]} {n : ℕ} (hn : 0 < n) :
    p.degree = n ↔ p.natDegree = n := by
  obtain rfl | h := eq_or_ne p 0
  · simp [hn.ne]
  · exact Polynomial.degree_eq_iff_natDegree_eq h

