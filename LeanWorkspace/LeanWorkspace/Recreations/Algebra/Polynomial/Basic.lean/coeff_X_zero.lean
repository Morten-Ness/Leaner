import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeff_X_zero : Polynomial.coeff (Polynomial.X : R[X]) 0 = 0 := Polynomial.coeff_monomial

