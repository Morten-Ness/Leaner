import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeff_X : Polynomial.coeff (Polynomial.X : R[X]) n = if 1 = n then 1 else 0 := Polynomial.coeff_monomial

