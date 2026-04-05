import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_C_mul_X (a : R) (ha : a ≠ 0) : Polynomial.natDegree (Polynomial.C a * Polynomial.X) = 1 := by
  simpa only [pow_one] using Polynomial.natDegree_C_mul_X_pow 1 a ha

