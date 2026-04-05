import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable [Semiring R] [Semiring R₂]

variable [AddCommMonoid M] [AddCommMonoid M₂]

variable [Module R M] [Module R₂ M₂]

variable {σ₁₂ : R →+* R₂}

variable [DistribSMul S M₂] [SMulCommClass R₂ S M₂]

variable [DistribSMul T M₂] [SMulCommClass R₂ T M₂]

theorem coe_smul (a : S) (f : M →ₛₗ[σ₁₂] M₂) : (a • f : M →ₛₗ[σ₁₂] M₂) = a • (f : M → M₂) := rfl

