import Mathlib

open scoped Polynomial

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem derivative_expand (f : R[X]) : Polynomial.derivative (Polynomial.expand R p f) =
    Polynomial.expand R p (Polynomial.derivative f) * (p * (Polynomial.X ^ (p - 1) : R[X])) := by
  rw [Polynomial.coe_expand, derivative_eval₂_C, derivative_pow, C_eq_natCast, derivative_X, mul_one]

