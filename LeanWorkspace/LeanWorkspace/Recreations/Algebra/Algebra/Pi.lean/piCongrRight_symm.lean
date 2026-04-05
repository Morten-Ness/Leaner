import Mathlib

variable {α β R ι : Type*} {A₁ A₂ A₃ : ι → Type*}

variable [CommSemiring R] [∀ i, Semiring (A₁ i)] [∀ i, Semiring (A₂ i)] [∀ i, Semiring (A₃ i)]

variable [∀ i, Algebra R (A₁ i)] [∀ i, Algebra R (A₂ i)] [∀ i, Algebra R (A₃ i)]

theorem piCongrRight_symm (e : ∀ i, A₁ i ≃ₐ[R] A₂ i) :
    (AlgEquiv.piCongrRight e).symm = AlgEquiv.piCongrRight fun i ↦ (e i).symm := rfl

