import Mathlib

variable {R S : Type*} {M N : Type u} [Semiring R] [Semiring S] {σ : R →+* S}
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module S N]
  {L : Type v} [AddCommMonoid L] [Module S L]

theorem spanFinrank_top (p : Submodule R M) : (⊤ : Submodule R p).spanFinrank = p.spanFinrank := by
  simp [Submodule.spanFinrank]

