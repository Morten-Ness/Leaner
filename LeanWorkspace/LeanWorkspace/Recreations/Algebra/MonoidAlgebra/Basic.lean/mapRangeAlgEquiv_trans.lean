import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B] [Semiring C]
  [Algebra R A] [Algebra R B] [Algebra R C] [Monoid M] [Monoid N]

theorem mapRangeAlgEquiv_trans (e₁ : A ≃ₐ[R] B) (e₂ : B ≃ₐ[R] C) :
    MonoidAlgebra.mapAlgEquiv R M (e₁.trans e₂) =
      (MonoidAlgebra.mapAlgEquiv R M e₁).trans (MonoidAlgebra.mapAlgEquiv R M e₂) := by ext; simp

