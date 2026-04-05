import Mathlib

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}

variable {K : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable {V : Type*} {V₂ : Type*}

variable [Semiring R] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable {module_M : Module R M} {module_M₂ : Module R₂ M₂} {module_M₃ : Module R₃ M₃}

variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}

variable {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable {σ₃₂ : R₃ →+* R₂}

variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}

variable {re₂₃ : RingHomInvPair σ₂₃ σ₃₂} {re₃₂ : RingHomInvPair σ₃₂ σ₂₃}

variable (e : M ≃ₛₗ[σ₁₂] M₂) (e'' : M₂ ≃ₛₗ[σ₂₃] M₃)

theorem ker : LinearMap.ker (e : M →ₛₗ[σ₁₂] M₂) = ⊥ := LinearMap.ker_eq_bot_of_injective e.toEquiv.injective

