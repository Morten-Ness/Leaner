import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_mul_monomial_zero (p : R[X]) (d : ℕ) (r : R) :
    coeff (p * monomial 0 r) d = coeff p d * r := Polynomial.coeff_mul_monomial p 0 d r

-- This can already be proved by `simp`.

