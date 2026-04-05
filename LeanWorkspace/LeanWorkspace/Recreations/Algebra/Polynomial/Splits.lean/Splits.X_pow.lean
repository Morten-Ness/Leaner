import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem Splits.X_pow (n : ℕ) : Polynomial.Splits (X ^ n : R[X]) := Polynomial.Splits.X.pow n

