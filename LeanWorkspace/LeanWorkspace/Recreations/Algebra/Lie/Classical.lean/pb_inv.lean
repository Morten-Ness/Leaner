import Mathlib

open scoped Matrix

variable (n p q l : Type*) (R : Type u₂)

variable [DecidableEq n] [DecidableEq p] [DecidableEq q] [DecidableEq l]

variable [CommRing R]

variable [Fintype p] [Fintype q]

variable [Fintype l]

theorem pb_inv [Invertible (2 : R)] : LieAlgebra.Orthogonal.PB l R * Matrix.fromBlocks 1 0 0 (⅟(LieAlgebra.Orthogonal.PD l R)) = 1 := by
  rw [LieAlgebra.Orthogonal.PB, Matrix.fromBlocks_multiply, mul_invOf_self]
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.zero_mul, zero_add, add_zero,
    Matrix.fromBlocks_one]

