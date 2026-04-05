import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable [Semiring R₁] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [AddCommGroup N₂] [AddCommGroup N₃]

variable [Module R₁ M] [Module R₂ M₂] [Module R₃ M₃]

variable [Module R₂ N₂] [Module R₃ N₃]

variable {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

theorem comp_zero (g : M₂ →ₛₗ[σ₂₃] M₃) : (g.comp (0 : M →ₛₗ[σ₁₂] M₂) : M →ₛₗ[σ₁₃] M₃) = 0 := LinearMap.ext fun c ↦ by rw [LinearMap.comp_apply, LinearMap.zero_apply, LinearMap.zero_apply, LinearMap.map_zero g]

