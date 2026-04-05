import Mathlib

variable (R M N) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

variable {ι} [Finite ι]

theorem LinearEquiv.finitePresentation_iff (e : M ≃ₗ[R] N) :
    Module.FinitePresentation R M ↔ Module.FinitePresentation R N := ⟨fun _ ↦ .of_equiv e, fun _ ↦ .of_equiv e.symm⟩

