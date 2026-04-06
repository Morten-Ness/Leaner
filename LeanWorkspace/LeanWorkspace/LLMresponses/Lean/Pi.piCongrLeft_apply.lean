import Mathlib

variable {α β R ι : Type*} {A₁ A₂ A₃ : ι → Type*}

variable [CommSemiring R] [∀ i, Semiring (A₁ i)] [∀ i, Semiring (A₂ i)] [∀ i, Semiring (A₃ i)]

variable [∀ i, Algebra R (A₁ i)] [∀ i, Algebra R (A₂ i)] [∀ i, Algebra R (A₃ i)]

theorem piCongrLeft_apply {ι' : Type*} (e : ι' ≃ ι) (x : Π i, A₁ (e i)) :
    AlgEquiv.piCongrLeft R A₁ e x = Equiv.piCongrLeft _ _ x := rfl
