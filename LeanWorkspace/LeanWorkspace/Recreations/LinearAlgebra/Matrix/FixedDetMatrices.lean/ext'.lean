import Mathlib

variable (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R]

theorem ext' {m : R} {A B : FixedDetMatrix n R m} (h : A.1 = B.1) : A = B := by
  cases A; cases B
  congr

