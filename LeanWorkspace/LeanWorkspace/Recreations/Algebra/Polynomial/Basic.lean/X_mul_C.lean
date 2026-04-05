import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem X_mul_C (r : R) : Polynomial.X * Polynomial.C r = Polynomial.C r * Polynomial.X := Polynomial.X_mul

