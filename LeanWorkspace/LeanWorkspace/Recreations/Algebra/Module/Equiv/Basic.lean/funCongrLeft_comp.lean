import Mathlib

variable {R : Type*} {R₂ : Type*}

variable {K : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable (R M) [Semiring R] [AddCommMonoid M] [Module R M]

variable {m n p : Type*}

theorem funCongrLeft_comp (e₁ : m ≃ n) (e₂ : n ≃ p) :
    LinearEquiv.funCongrLeft R M (Equiv.trans e₁ e₂) =
      LinearEquiv.trans (LinearEquiv.funCongrLeft R M e₂) (LinearEquiv.funCongrLeft R M e₁) := rfl

