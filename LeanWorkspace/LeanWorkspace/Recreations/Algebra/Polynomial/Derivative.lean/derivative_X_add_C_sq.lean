import Mathlib

open scoped Nat

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommSemiring R]

theorem derivative_X_add_C_sq (c : R) : Polynomial.derivative ((Polynomial.X + Polynomial.C c) ^ 2) = Polynomial.C 2 * (Polynomial.X + Polynomial.C c) := by
  rw [Polynomial.derivative_sq, Polynomial.derivative_X_add_C, mul_one]

