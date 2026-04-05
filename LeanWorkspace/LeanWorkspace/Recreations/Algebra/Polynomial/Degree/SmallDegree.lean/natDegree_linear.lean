import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem natDegree_linear (ha : a ≠ 0) : natDegree (Polynomial.C a * Polynomial.X + Polynomial.C b) = 1 := by
  rw [natDegree_add_C, natDegree_C_mul_X a ha]

