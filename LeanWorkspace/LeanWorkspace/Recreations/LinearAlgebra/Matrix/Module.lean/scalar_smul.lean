import Mathlib

variable {ι R M N P : Type*} [Ring R] [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

theorem scalar_smul (r : R) (v : ι → M) :
    Matrix.scalar ι r • v = r • v := by
  simp

scoped instance (S : Type*) [Ring S] [SMul R S] [Matrix.Module S M] [IsScalarTower R S M] :
    IsScalarTower R (Matrix ι ι S) (ι → M) where
  smul_assoc _ _ _ := by ext; simp [Finset.smul_sum]

