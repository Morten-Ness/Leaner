import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommSemiring R]

theorem derivative_sq (p : R[X]) : Polynomial.derivative (p ^ 2) = Polynomial.C 2 * p * Polynomial.derivative p := by
  rw [Polynomial.derivative_pow_succ, Nat.cast_one, one_add_one_eq_two, pow_one]

