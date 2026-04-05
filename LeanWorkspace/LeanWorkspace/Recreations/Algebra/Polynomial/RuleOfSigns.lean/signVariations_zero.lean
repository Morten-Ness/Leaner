import Mathlib

variable {R : Type*} [Semiring R] [LinearOrder R] (P : Polynomial R)

theorem signVariations_zero : Polynomial.signVariations (0 : R[X]) = 0 := by
  simp [Polynomial.signVariations]

