import Mathlib

variable {R S : Type*} {M N : Type u} [Semiring R] [Semiring S] {σ : R →+* S}
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module S N]
  {L : Type v} [AddCommMonoid L] [Module S L]

theorem spanRank_eq_of_equiv
    {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e : M ≃ₛₗ[σ] N) : (⊤ : Submodule R M).spanRank = (⊤ : Submodule S N).spanRank := by
  rw [← Submodule.spanRank_map_eq_of_injective e.toLinearMap e.injective ⊤, map_top, LinearEquiv.range]

