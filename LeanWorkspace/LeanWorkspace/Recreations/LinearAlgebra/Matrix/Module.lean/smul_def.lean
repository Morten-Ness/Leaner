import Mathlib

variable {ι R M N P : Type*} [Ring R] [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

theorem smul_def (N : Matrix ι ι R) (v : ι → M) :
    N • v = fun i ↦ ∑ j : ι, N i j • v j := rfl

