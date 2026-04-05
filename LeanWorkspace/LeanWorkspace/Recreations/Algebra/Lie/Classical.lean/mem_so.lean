import Mathlib

open scoped Matrix

variable (n p q l : Type*) (R : Type u₂)

variable [DecidableEq n] [DecidableEq p] [DecidableEq q] [DecidableEq l]

variable [CommRing R]

theorem mem_so [Fintype n] (A : Matrix n n R) : A ∈ LieAlgebra.Orthogonal.so n R ↔ Aᵀ = -A := by
  rw [LieAlgebra.Orthogonal.so, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, Matrix.mul_one, Matrix.one_mul]

