import Mathlib

open scoped Matrix

variable (n p q l : Type*) (R : Type u₂)

variable [DecidableEq n] [DecidableEq p] [DecidableEq q] [DecidableEq l]

variable [CommRing R]

variable {n R} [Fintype n] (i j k : n)

theorem singleSubSingle_add_singleSubSingle (r : R) :
    LieAlgebra.SpecialLinear.singleSubSingle i j r + LieAlgebra.SpecialLinear.singleSubSingle j k r = LieAlgebra.SpecialLinear.singleSubSingle i k r := by
  ext : 1; simp

