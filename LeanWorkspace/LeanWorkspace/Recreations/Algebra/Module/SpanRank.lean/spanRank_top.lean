import Mathlib

variable {R S : Type*} {M N : Type u} [Semiring R] [Semiring S] {σ : R →+* S}
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module S N]
  {L : Type v} [AddCommMonoid L] [Module S L]

theorem spanRank_top (p : Submodule R M) : (⊤ : Submodule R p).spanRank = p.spanRank := by
  simpa using (Submodule.spanRank_map_eq_of_injective _ p.subtype_injective ⊤).symm

