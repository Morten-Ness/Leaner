import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeff_ofNat_zero (a : ℕ) [a.AtLeastTwo] :
    Polynomial.coeff (ofNat(a) : R[X]) 0 = ofNat(a) := Polynomial.coeff_monomial

