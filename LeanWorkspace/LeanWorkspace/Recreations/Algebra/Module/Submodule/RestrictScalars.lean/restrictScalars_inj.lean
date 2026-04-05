import Mathlib

variable (S : Type*) {R M : Type*} [Semiring R] [AddCommMonoid M] [Semiring S]
  [Module S M] [Module R M] [SMul S R] [IsScalarTower S R M]

theorem restrictScalars_inj {V₁ V₂ : Submodule R M} :
    Submodule.restrictScalars S V₁ = Submodule.restrictScalars S V₂ ↔ V₁ = V₂ := (Submodule.restrictScalars_injective S _ _).eq_iff

