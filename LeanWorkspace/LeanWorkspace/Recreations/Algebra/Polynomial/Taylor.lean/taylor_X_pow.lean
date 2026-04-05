import Mathlib

variable {R : Type*} [Semiring R] (r : R) (f : R[X])

theorem taylor_X_pow (n : ℕ) : Polynomial.taylor r (X ^ n) = (X + C r) ^ n := X_pow_comp

