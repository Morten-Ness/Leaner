import Mathlib

variable {R : Type*} {R₂ : Type*}

variable {K : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable (R M) [Semiring R] [AddCommMonoid M] [Module R M]

variable {m n p : Type*}

theorem funCongrLeft_apply (e : m ≃ n) (x : n → M) : LinearEquiv.funCongrLeft R M e x = LinearMap.funLeft R M e x := rfl

