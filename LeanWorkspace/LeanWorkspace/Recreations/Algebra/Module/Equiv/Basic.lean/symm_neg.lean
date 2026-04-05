import Mathlib

variable {R : Type*} {R₂ : Type*}

variable {K : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable (R) [Semiring R] [AddCommGroup M] [Module R M]

theorem symm_neg : (LinearEquiv.neg R : M ≃ₗ[R] M).symm = LinearEquiv.neg R := rfl

