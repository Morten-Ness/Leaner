import Mathlib

open scoped Matrix

variable (n p q l : Type*) (R : Type u₂)

variable [DecidableEq n] [DecidableEq p] [DecidableEq q] [DecidableEq l]

variable [CommRing R]

variable {n R} [Fintype n] (i j k : n)

theorem val_singleSubSingle (r : R) :
    (LieAlgebra.SpecialLinear.singleSubSingle i j r).val = Matrix.single i i r - Matrix.single j j r := rfl

