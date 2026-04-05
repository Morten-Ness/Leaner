import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem X_pow_mul_assoc_C {n : ℕ} (r : R) : p * Polynomial.X ^ n * Polynomial.C r = p * Polynomial.C r * Polynomial.X ^ n := Polynomial.X_pow_mul_assoc

