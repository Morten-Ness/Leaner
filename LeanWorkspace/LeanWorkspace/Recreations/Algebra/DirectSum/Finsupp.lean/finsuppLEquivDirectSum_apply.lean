import Mathlib

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

variable (R M) (ι : Type*) [DecidableEq ι]

theorem finsuppLEquivDirectSum_apply (m : ι →₀ M) (i : ι) :
    finsuppLEquivDirectSum R M ι m i = m i := by
  rfl

