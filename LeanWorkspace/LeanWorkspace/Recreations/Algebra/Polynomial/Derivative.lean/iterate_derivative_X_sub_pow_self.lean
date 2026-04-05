import Mathlib

open scoped Nat

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R]

theorem iterate_derivative_X_sub_pow_self (n : ℕ) (c : R) :
    Polynomial.derivative^[n] ((Polynomial.X - Polynomial.C c) ^ n) = n.factorial := by
  rw [Polynomial.iterate_derivative_X_sub_pow, n.sub_self, pow_zero, nsmul_one, n.descFactorial_self]

