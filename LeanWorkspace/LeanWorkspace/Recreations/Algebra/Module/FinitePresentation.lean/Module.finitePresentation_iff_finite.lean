import Mathlib

variable (R M N) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem Module.finitePresentation_iff_finite [IsNoetherianRing R] :
    Module.FinitePresentation R M ↔ Module.Finite R M := ⟨fun _ ↦ inferInstance, fun _ ↦ finitePresentation_of_finite R M⟩

