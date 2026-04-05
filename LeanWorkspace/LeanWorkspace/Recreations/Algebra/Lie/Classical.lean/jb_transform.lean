import Mathlib

open scoped Matrix

variable (n p q l : Type*) (R : Type u₂)

variable [DecidableEq n] [DecidableEq p] [DecidableEq q] [DecidableEq l]

variable [CommRing R]

variable [Fintype p] [Fintype q]

variable [Fintype l]

theorem jb_transform : (LieAlgebra.Orthogonal.PB l R)ᵀ * LieAlgebra.Orthogonal.JB l R * LieAlgebra.Orthogonal.PB l R = (2 : R) • Matrix.fromBlocks 1 0 0 (LieAlgebra.Orthogonal.S l R) := by
  simp [LieAlgebra.Orthogonal.PB, LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.jd_transform, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_smul]

