import Mathlib

variable (R : Type u) [CommSemiring R]

variable (X : Type v)

variable (X : Type u)

theorem cardinalMk_eq [IsEmpty X] : #(FreeAlgebra R X) = #R := by
  simp

