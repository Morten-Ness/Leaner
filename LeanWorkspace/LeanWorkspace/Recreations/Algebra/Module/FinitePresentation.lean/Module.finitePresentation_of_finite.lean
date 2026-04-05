import Mathlib

variable (R M N) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem Module.finitePresentation_of_finite [IsNoetherianRing R] [h : Module.Finite R M] :
    Module.FinitePresentation R M := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, hs, IsNoetherian.noetherian _⟩

