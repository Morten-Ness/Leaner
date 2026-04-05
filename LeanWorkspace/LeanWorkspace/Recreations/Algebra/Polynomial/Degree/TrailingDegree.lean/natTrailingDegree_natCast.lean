import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natTrailingDegree_natCast (n : ℕ) : Polynomial.natTrailingDegree (n : R[X]) = 0 := by
  simp only [← C_eq_natCast, Polynomial.natTrailingDegree_C]

