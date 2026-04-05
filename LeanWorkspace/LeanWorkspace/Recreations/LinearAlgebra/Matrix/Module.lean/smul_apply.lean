import Mathlib

variable {ι R M N P : Type*} [Ring R] [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

theorem smul_apply (N : Matrix ι ι R) (v : ι → M) (i : ι) :
    (N • v) i = ∑ j : ι, N i j • v j := rfl

