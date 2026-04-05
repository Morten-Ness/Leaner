import Mathlib

variable {α β R ι : Type*} {A₁ A₂ A₃ : ι → Type*}

variable [CommSemiring R] [∀ i, Semiring (A₁ i)] [∀ i, Semiring (A₂ i)] [∀ i, Semiring (A₃ i)]

variable [∀ i, Algebra R (A₁ i)] [∀ i, Algebra R (A₂ i)] [∀ i, Algebra R (A₃ i)]

theorem piCongrLeft_symm_apply {ι' : Type*} (e : ι' ≃ ι) (x : Π i, A₁ i) :
    (AlgEquiv.piCongrLeft R A₁ e).symm x = (Equiv.piCongrLeft _ _).symm x := rfl

