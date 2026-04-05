import Mathlib

variable {R : Type*} {R₂ : Type*}

variable {K : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable [Semiring R] [Semiring S] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]

variable [Module R M]

theorem pow_apply (e : M ≃ₗ[R] M) (n : ℕ) (m : M) : (e ^ n) m = e^[n] m := congr_fun (LinearEquiv.coe_pow e n) m

