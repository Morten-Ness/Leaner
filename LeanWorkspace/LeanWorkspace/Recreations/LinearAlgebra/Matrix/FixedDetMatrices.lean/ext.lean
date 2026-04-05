import Mathlib

variable (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R]

theorem ext {m : R} {A B : FixedDetMatrix n R m} (h : ∀ i j, A.1 i j = B.1 i j) : A = B := by
  apply FixedDetMatrices.ext'
  ext i j
  apply h

