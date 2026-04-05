import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R]

theorem natDegree_intCast (n : ℤ) : Polynomial.natDegree (n : R[X]) = 0 := by
  rw [← Polynomial.C_eq_intCast, Polynomial.natDegree_C]

