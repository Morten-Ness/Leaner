import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_natCast (n : ℕ) : Polynomial.natDegree (n : R[X]) = 0 := by
  simp only [← C_eq_natCast, Polynomial.natDegree_C]

