import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R]

theorem degree_neg (p : R[X]) : Polynomial.degree (-p) = Polynomial.degree p := by unfold Polynomial.degree; rw [support_neg]

