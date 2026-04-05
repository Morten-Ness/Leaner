import Mathlib

variable {R : Type*} [CommSemiring R]

variable {k l m n : Type*} [DecidableEq n] [Fintype n]

theorem LinearMap.toMatrix'_algebraMap (x : R) :
    LinearMap.toMatrix' (algebraMap R (Module.End R (n → R)) x) = Matrix.scalar n x := by
  simp [Module.algebraMap_end_eq_smul_id, smul_eq_diagonal_mul]

