import Mathlib

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}

variable {K : Type*}

variable {M : Type*} {M₂ : Type*} {M₃ : Type*}

variable {V : Type*} {V₂ : Type*}

variable [Semiring R] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

variable {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}

variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]

theorem range_neg {R : Type*} {R₂ : Type*} {M : Type*} {M₂ : Type*} [Semiring R] [Ring R₂]
    [AddCommMonoid M] [AddCommGroup M₂] [Module R M] [Module R₂ M₂] {τ₁₂ : R →+* R₂}
    [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : LinearMap.range (-f) = LinearMap.range f := by
  change LinearMap.range ((-LinearMap.id : M₂ →ₗ[R₂] M₂).comp f) = _
  rw [LinearMap.range_comp, Submodule.map_neg, Submodule.map_id]

