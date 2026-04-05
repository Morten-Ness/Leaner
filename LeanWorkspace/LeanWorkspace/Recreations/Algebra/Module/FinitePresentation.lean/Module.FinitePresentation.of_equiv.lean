import Mathlib

variable (R M N) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

variable {ι} [Finite ι]

theorem Module.FinitePresentation.of_equiv (e : M ≃ₗ[R] N) [Module.FinitePresentation R M] :
    Module.FinitePresentation R N := by
  simp [← Module.FinitePresentation.fg_ker_iff e.toLinearMap e.surjective, Submodule.fg_bot]

