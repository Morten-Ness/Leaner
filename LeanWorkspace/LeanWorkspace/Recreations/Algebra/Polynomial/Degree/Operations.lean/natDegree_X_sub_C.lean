import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R]

variable [Nontrivial R]

theorem natDegree_X_sub_C (x : R) : (Polynomial.X - Polynomial.C x).natDegree = 1 := by
  rw [Polynomial.natDegree_sub_C, natDegree_X]

