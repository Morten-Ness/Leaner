import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable [Semiring R] [Semiring S]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₂] [Module S M₃]

variable (σ : R →+* S)

variable (fₗ : M →ₗ[R] M₂) (f g : M →ₛₗ[σ] M₃)

theorem ext_ring {f g : R →ₛₗ[σ] M₃} (h : f 1 = g 1) : f = g := LinearMap.ext fun x ↦ by rw [← mul_one x, ← smul_eq_mul, LinearMap.map_smulₛₗ f, LinearMap.map_smulₛₗ g, h]

