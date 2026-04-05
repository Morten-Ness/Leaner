import Mathlib

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [Semiring T]

variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

variable (b : Basis m R S) (c : Basis n S T)

theorem smulTower_leftMulMatrix_algebraMap_eq (x : S) (i j k) :
    Algebra.leftMulMatrix (b.smulTower c) (algebraMap _ _ x) (i, k) (j, k) = Algebra.leftMulMatrix b x i j := by
  rw [Algebra.smulTower_leftMulMatrix_algebraMap, blockDiagonal_apply_eq]

