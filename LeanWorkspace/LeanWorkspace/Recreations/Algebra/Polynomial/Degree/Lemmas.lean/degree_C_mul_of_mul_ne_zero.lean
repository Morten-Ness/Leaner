import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem degree_C_mul_of_mul_ne_zero (h : a * p.leadingCoeff ≠ 0) : (Polynomial.C a * p).degree = p.degree := by
  rw [degree_mul' (by simpa)]; simp [left_ne_zero_of_mul h]

