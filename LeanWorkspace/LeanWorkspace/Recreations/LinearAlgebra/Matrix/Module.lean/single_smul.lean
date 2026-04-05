import Mathlib

variable {ι R M N P : Type*} [Ring R] [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

theorem single_smul (i j : ι) (r : R) (v : ι → M) :
    Matrix.single i j r • v = Pi.single i (r • v j) := by
  ext i'
  dsimp
  rw [Fintype.sum_eq_single j fun j' hj => ?_]
  · obtain rfl | hi := eq_or_ne i i' <;> simp [*]
  · simp [hj.symm]

