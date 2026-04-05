import Mathlib

open scoped Nat

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R]

theorem iterate_derivative_X_sub_pow (n k : ℕ) (c : R) :
    Polynomial.derivative^[k] ((Polynomial.X - Polynomial.C c) ^ n) = n.descFactorial k • (Polynomial.X - Polynomial.C c) ^ (n - k) := by
  rw [sub_eq_add_neg, ← C_neg, Polynomial.iterate_derivative_X_add_pow]

