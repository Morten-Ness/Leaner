import Mathlib

variable {R : Type*} {R₂ : Type*}

variable {K : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₂]

variable (e : M ≃+ M₂)

theorem _root_.LinearEquiv.toAddEquiv_toNatLinearEquiv (e : M ≃ₗ[ℕ] M₂) :
    AddEquiv.toNatLinearEquiv ↑e = e := DFunLike.coe_injective rfl

