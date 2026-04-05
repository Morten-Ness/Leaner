import Mathlib

variable {R : Type*} {R₂ : Type*}

variable {K : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable (R M) [Semiring R] [AddCommMonoid M] [Module R M]

variable {m n p : Type*}

theorem funCongrLeft_symm (e : m ≃ n) : (LinearEquiv.funCongrLeft R M e).symm = LinearEquiv.funCongrLeft R M e.symm := rfl

