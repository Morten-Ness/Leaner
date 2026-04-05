import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeff_X_one : Polynomial.coeff (Polynomial.X : R[X]) 1 = 1 := Polynomial.coeff_monomial

