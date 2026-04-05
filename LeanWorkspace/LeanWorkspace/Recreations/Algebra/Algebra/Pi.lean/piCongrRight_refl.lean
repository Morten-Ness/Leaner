import Mathlib

variable {α β R ι : Type*} {A₁ A₂ A₃ : ι → Type*}

variable [CommSemiring R] [∀ i, Semiring (A₁ i)] [∀ i, Semiring (A₂ i)] [∀ i, Semiring (A₃ i)]

variable [∀ i, Algebra R (A₁ i)] [∀ i, Algebra R (A₂ i)] [∀ i, Algebra R (A₃ i)]

theorem piCongrRight_refl :
    (AlgEquiv.piCongrRight fun i ↦ (AlgEquiv.refl : A₁ i ≃ₐ[R] A₁ i)) = AlgEquiv.refl := rfl

