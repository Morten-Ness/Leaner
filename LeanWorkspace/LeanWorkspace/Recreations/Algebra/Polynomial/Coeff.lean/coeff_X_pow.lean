import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_X_pow (k n : ℕ) : coeff (Polynomial.X ^ k : R[X]) n = if n = k then 1 else 0 := by
  simp only [one_mul, map_one, ← Polynomial.coeff_C_mul_X_pow]

