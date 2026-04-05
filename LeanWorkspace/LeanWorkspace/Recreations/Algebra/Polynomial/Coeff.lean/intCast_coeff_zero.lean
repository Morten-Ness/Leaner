import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem intCast_coeff_zero {i : ℤ} {R : Type*} [Ring R] : (i : R[X]).coeff 0 = i := by
  cases i <;> simp

