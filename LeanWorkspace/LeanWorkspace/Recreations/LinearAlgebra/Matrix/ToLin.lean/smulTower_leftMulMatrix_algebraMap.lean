import Mathlib

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [Semiring T]

variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

variable (b : Basis m R S) (c : Basis n S T)

theorem smulTower_leftMulMatrix_algebraMap (x : S) :
    Algebra.leftMulMatrix (b.smulTower c) (algebraMap _ _ x) = blockDiagonal fun _ ↦ Algebra.leftMulMatrix b x := by
  ext ⟨i, k⟩ ⟨j, k'⟩
  rw [Algebra.smulTower_leftMulMatrix, AlgHom.commutes, blockDiagonal_apply, algebraMap_matrix_apply]
  split_ifs with h <;> simp only at h <;> simp

