import Mathlib

open scoped Matrix

variable (n p q l : Type*) (R : Type u₂)

variable [DecidableEq n] [DecidableEq p] [DecidableEq q] [DecidableEq l]

variable [CommRing R]

variable [Fintype p] [Fintype q]

theorem jd_transform [Fintype l] : (LieAlgebra.Orthogonal.PD l R)ᵀ * LieAlgebra.Orthogonal.JD l R * LieAlgebra.Orthogonal.PD l R = (2 : R) • LieAlgebra.Orthogonal.S l R := by
  have h : (LieAlgebra.Orthogonal.PD l R)ᵀ * LieAlgebra.Orthogonal.JD l R = Matrix.fromBlocks 1 1 1 (-1) := by
    simp [LieAlgebra.Orthogonal.PD, LieAlgebra.Orthogonal.JD, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  rw [h, LieAlgebra.Orthogonal.PD, LieAlgebra.Orthogonal.s_as_blocks, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]
  simp [two_smul]

