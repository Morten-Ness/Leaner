import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R]

variable [NoZeroDivisors R]

variable [NormalizationMonoid R]

theorem leadingCoeff_normalize (p : R[X]) :
    leadingCoeff (normalize p) = normalize (leadingCoeff p) := by simp [normalize_apply]

