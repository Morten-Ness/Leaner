import Mathlib

open scoped Matrix

variable (n p q l : Type*) (R : Type u₂)

variable [DecidableEq n] [DecidableEq p] [DecidableEq q] [DecidableEq l]

variable [CommRing R]

theorem sl_bracket [Fintype n] (A B : LieAlgebra.SpecialLinear.sl n R) : ⁅A, B⁆.val = A.val * B.val - B.val * A.val := rfl

