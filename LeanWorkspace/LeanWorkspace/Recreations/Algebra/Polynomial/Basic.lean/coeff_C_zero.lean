import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeff_C_zero : Polynomial.coeff (Polynomial.C a) 0 = a := Polynomial.coeff_monomial

