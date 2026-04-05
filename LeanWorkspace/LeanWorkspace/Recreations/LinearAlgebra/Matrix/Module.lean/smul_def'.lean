import Mathlib

variable {ι R M N P : Type*} [Ring R] [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

theorem smul_def' (N : Matrix ι ι R) (v : ι → M) : N • v = ∑ j : ι, fun i ↦ N i j • v j := by
  ext; simp [Matrix.Module.smul_def]

