import Mathlib

variable {R S M₁ M₂ : Type*} [CommSemiring R] [AddCommMonoid M₁] [Module R M₁]
  [AddCommMonoid M₂] [Module R M₂] [Semiring S] [Module S M₁] [Module S M₂]
  [SMulCommClass S R M₁] [SMulCommClass S R M₂] [SMul R S] [IsScalarTower R S M₁]
  [IsScalarTower R S M₂]

theorem symm_conjAlgEquiv (e : M₁ ≃ₗ[S] M₂) : (e.conjAlgEquiv R).symm = e.symm.conjAlgEquiv R := rfl

