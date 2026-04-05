import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R]

theorem leadingCoeff_neg (p : R[X]) : (-p).leadingCoeff = -p.leadingCoeff := by
  rw [Polynomial.leadingCoeff, Polynomial.leadingCoeff, Polynomial.natDegree_neg, coeff_neg]

