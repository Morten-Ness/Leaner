import Mathlib

open scoped Polynomial

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem expand_mul (f : R[X]) : Polynomial.expand R (p * q) f = Polynomial.expand R p (Polynomial.expand R q f) := (Polynomial.expand_expand p q f).symm

