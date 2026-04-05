import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [DivisionRing R]

theorem qsmul_eq_C_mul (a : ℚ) (f : R[X]) : a • f = Polynomial.C (a : R) * f := by
  rw [← Rat.smul_one_eq_cast, ← Polynomial.smul_C, Polynomial.C_1, smul_one_mul]

