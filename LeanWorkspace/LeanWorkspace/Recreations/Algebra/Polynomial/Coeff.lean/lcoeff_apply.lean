import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem lcoeff_apply (n : ℕ) (f : R[X]) : Polynomial.lcoeff R n f = coeff f n := rfl

