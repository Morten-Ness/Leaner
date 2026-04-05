import Mathlib

variable {ι R M N P : Type*} [Ring R] [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

theorem diagonal_const_smul (r : R) (v : ι → M) :
    diagonal (fun _ : ι ↦ r) • v = r • v := by
  ext i
  simp [Matrix.diagonal_apply]

