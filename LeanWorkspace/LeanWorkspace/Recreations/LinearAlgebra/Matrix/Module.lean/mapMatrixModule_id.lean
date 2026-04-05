import Mathlib

variable {ι R M N P : Type*} [Ring R] [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

theorem mapMatrixModule_id :
    LinearMap.id.mapMatrixModule ι = .id (R := Matrix ι ι R) (M := ι → M) := by
  ext; simp

