import Mathlib

open scoped Matrix

variable (n p q l : Type*) (R : Type u₂)

variable [DecidableEq n] [DecidableEq p] [DecidableEq q] [DecidableEq l]

variable [CommRing R]

variable {n R} [Fintype n] (i j k : n)

theorem val_single (h : i ≠ j) (r : R) : (LieAlgebra.SpecialLinear.single i j h r).val = Matrix.single i j r := rfl

