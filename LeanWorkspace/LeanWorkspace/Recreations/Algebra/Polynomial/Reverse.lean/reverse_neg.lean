import Mathlib

open scoped Polynomial

variable {R : Type*} [Ring R]

theorem reverse_neg (f : R[X]) : Polynomial.reverse (-f) = -Polynomial.reverse f := by
  rw [Polynomial.reverse, Polynomial.reverse, Polynomial.reflect_neg, natDegree_neg]

