import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_monomial_zero_mul (p : R[X]) (d : ℕ) (r : R) :
    coeff (monomial 0 r * p) d = r * coeff p d := Polynomial.coeff_monomial_mul p 0 d r

