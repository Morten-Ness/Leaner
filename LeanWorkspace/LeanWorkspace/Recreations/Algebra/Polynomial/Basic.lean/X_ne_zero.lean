import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R]

theorem X_ne_zero [Nontrivial R] : (Polynomial.X : R[X]) ≠ 0 := mt (congr_arg fun p => Polynomial.coeff p 1) (by simp)

