import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R]

theorem natDegree_neg (p : R[X]) : Polynomial.natDegree (-p) = Polynomial.natDegree p := by simp [Polynomial.natDegree]

