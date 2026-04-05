import Mathlib

variable {R S : Type*} {M N : Type u} [Semiring R] [Semiring S] {σ : R →+* S}
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module S N]
  {L : Type v} [AddCommMonoid L] [Module S L]

theorem spanRank_map_le [RingHomSurjective σ] (f : M →ₛₗ[σ] N) (p : Submodule R M) :
    (p.map f).spanRank ≤ p.spanRank := by
  simpa using Submodule.lift_spanRank_map_le f p

