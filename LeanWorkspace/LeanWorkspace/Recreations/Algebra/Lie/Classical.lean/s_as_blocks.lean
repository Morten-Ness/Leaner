import Mathlib

open scoped Matrix

variable (n p q l : Type*) (R : Type u₂)

variable [DecidableEq n] [DecidableEq p] [DecidableEq q] [DecidableEq l]

variable [CommRing R]

variable [Fintype p] [Fintype q]

theorem s_as_blocks : LieAlgebra.Orthogonal.S l R = Matrix.fromBlocks 1 0 0 (-1) := by
  rw [← Matrix.diagonal_one, Matrix.diagonal_neg, Matrix.fromBlocks_diagonal]
  rfl

