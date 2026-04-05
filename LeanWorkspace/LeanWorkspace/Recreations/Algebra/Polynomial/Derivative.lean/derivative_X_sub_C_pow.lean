import Mathlib

open scoped Nat

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R]

theorem derivative_X_sub_C_pow (c : R) (m : ℕ) :
    Polynomial.derivative ((Polynomial.X - Polynomial.C c) ^ m) = Polynomial.C (m : R) * (Polynomial.X - Polynomial.C c) ^ (m - 1) := by
  rw [Polynomial.derivative_pow, Polynomial.derivative_X_sub_C, mul_one]

