import Mathlib

open scoped Matrix

variable (n p q l : Type*) (R : Type u₂)

variable [DecidableEq n] [DecidableEq p] [DecidableEq q] [DecidableEq l]

variable [CommRing R]

variable [Fintype p] [Fintype q]

set_option backward.isDefEq.respectTransparency false in
theorem pd_inv [Fintype l] [Invertible (2 : R)] : LieAlgebra.Orthogonal.PD l R * ⅟(2 : R) • (LieAlgebra.Orthogonal.PD l R)ᵀ = 1 := by
  rw [LieAlgebra.Orthogonal.PD, Matrix.fromBlocks_transpose, Matrix.fromBlocks_smul,
    Matrix.fromBlocks_multiply]
  simp

