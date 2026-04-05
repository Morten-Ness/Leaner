import Mathlib

variable (R M N) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

variable {ι} [Finite ι]

theorem Module.FinitePresentation.fg_ker_iff [Module.FinitePresentation R M]
    (l : M →ₗ[R] N) (hl : Function.Surjective l) :
    Submodule.FG (LinearMap.ker l) ↔ Module.FinitePresentation R N := ⟨finitePresentation_of_surjective l hl, fun _ ↦ fg_ker l hl⟩

