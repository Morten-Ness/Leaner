import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R]

variable [NoZeroDivisors R]

variable [NormalizationMonoid R]

theorem coe_normUnit {p : R[X]} : (normUnit p : R[X]) = Polynomial.C ↑(normUnit p.leadingCoeff) := by
  simp [normUnit]

