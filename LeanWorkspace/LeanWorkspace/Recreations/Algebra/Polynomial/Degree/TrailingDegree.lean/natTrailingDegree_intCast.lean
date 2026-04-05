import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Ring R]

theorem natTrailingDegree_intCast (n : ℤ) : Polynomial.natTrailingDegree (n : R[X]) = 0 := by
  simp only [← Polynomial.C_eq_intCast, Polynomial.natTrailingDegree_C]

