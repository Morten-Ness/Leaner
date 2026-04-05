import Mathlib

variable (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R]

theorem smul_coe (m : R) (g : SpecialLinearGroup n R) (A : FixedDetMatrix n R m) :
    (g • A).1 = g * A.1 := by
  rw [FixedDetMatrices.smul_def]

