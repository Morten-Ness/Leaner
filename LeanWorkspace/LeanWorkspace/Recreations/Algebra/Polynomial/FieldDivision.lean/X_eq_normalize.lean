import Mathlib

open scoped Nat

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R]

variable [NoZeroDivisors R]

variable [NormalizationMonoid R]

theorem X_eq_normalize : (Polynomial.X : Polynomial R) = normalize Polynomial.X := by
  simp only [normalize_apply, Polynomial.normUnit_X, Units.val_one, mul_one]

