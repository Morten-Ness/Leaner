import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem X_pow_mul_C (r : R) (n : ℕ) : Polynomial.X ^ n * Polynomial.C r = Polynomial.C r * Polynomial.X ^ n := Polynomial.X_pow_mul

