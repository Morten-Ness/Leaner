import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem divX_C_mul_X_pow : Polynomial.divX (Polynomial.C a * Polynomial.X ^ n) = if n = 0 then 0 else Polynomial.C a * Polynomial.X ^ (n - 1) := by
  simp only [Polynomial.divX_C_mul, Polynomial.divX_X_pow, mul_ite, mul_zero]

