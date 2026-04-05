import Mathlib

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

variable (R M) (ι : Type*) [DecidableEq ι]

theorem lmap_finsuppLEquivDirectSum_eq {N : Type*} [AddCommMonoid N] [Module R N]
    (ε : M →ₗ[R] N) (m : ι →₀ M) :
    (lmap fun _ ↦ ε) ((finsuppLEquivDirectSum R M ι) m) =
      (finsuppLEquivDirectSum R N ι) (m.mapRange ⇑ε ε.map_zero) := by
  ext i
  rfl

