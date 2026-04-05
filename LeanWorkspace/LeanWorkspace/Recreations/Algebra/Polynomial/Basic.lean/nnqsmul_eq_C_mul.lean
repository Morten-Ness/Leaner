import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [DivisionSemiring R]

theorem nnqsmul_eq_C_mul (q : ℚ≥0) (f : R[X]) : q • f = Polynomial.C (q : R) * f := by
  rw [← NNRat.smul_one_eq_cast, ← Polynomial.smul_C, Polynomial.C_1, smul_one_mul]

