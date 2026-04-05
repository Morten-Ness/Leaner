import Mathlib

open scoped Nat

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R]

variable [NoZeroDivisors R]

variable [NormalizationMonoid R]

theorem normUnit_X : normUnit (Polynomial.X : Polynomial R) = 1 := by
  have := Polynomial.coe_normUnit (R := R) (p := Polynomial.X)
  rwa [leadingCoeff_X, normUnit_one, Units.val_one, map_one, Units.val_eq_one] at this

