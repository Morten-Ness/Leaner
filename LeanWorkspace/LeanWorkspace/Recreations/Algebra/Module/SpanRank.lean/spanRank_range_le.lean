import Mathlib

variable {R S : Type*} {M N : Type u} [Semiring R] [Semiring S] {σ : R →+* S}
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module S N]
  {L : Type v} [AddCommMonoid L] [Module S L]

theorem spanRank_range_le [RingHomSurjective σ] (f : M →ₛₗ[σ] N) :
    (LinearMap.range f).spanRank ≤ (⊤ : Submodule R M).spanRank := by
  simpa using Submodule.spanRank_map_le f ⊤

