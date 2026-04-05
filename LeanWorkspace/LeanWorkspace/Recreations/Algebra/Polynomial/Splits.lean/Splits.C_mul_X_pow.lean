import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem Splits.C_mul_X_pow (a : R) (n : ℕ) : Polynomial.Splits (C a * X ^ n) := (Polynomial.Splits.X_pow n).C_mul a

