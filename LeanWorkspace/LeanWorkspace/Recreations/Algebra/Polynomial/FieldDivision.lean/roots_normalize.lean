import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R]

variable [NoZeroDivisors R]

variable [NormalizationMonoid R]

theorem roots_normalize {R} [CommRing R] [IsDomain R] [NormalizationMonoid R] {p : R[X]} :
    (normalize p).roots = p.roots := by
  rw [normalize_apply, mul_comm, Polynomial.coe_normUnit, roots_C_mul _ (normUnit (leadingCoeff p)).ne_zero]

