import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem Splits.monomial (n : ℕ) (a : R) : Polynomial.Splits (monomial n a) := by
  simp [← C_mul_X_pow_eq_monomial]

