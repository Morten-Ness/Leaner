import Mathlib

open scoped Polynomial

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem contract_one {f : R[X]} : Polynomial.contract 1 f = f := ext fun n ↦ by rw [Polynomial.coeff_contract one_ne_zero, mul_one]

