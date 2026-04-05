import Mathlib

variable {ι R M N P : Type*} [Ring R] [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

theorem mapMatrixModule_id_apply (v : ι → M) :
    LinearMap.id.mapMatrixModule ι (R := R) v = v := by
  simp

