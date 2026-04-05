import Mathlib

variable {α β R ι : Type*} {A₁ A₂ A₃ : ι → Type*}

variable [CommSemiring R] [∀ i, Semiring (A₁ i)] [∀ i, Semiring (A₂ i)] [∀ i, Semiring (A₃ i)]

variable [∀ i, Algebra R (A₁ i)] [∀ i, Algebra R (A₂ i)] [∀ i, Algebra R (A₃ i)]

theorem piCongrRight_trans (e₁ : ∀ i, A₁ i ≃ₐ[R] A₂ i) (e₂ : ∀ i, A₂ i ≃ₐ[R] A₃ i) :
    (AlgEquiv.piCongrRight e₁).trans (AlgEquiv.piCongrRight e₂) = AlgEquiv.piCongrRight fun i ↦ (e₁ i).trans (e₂ i) := rfl

