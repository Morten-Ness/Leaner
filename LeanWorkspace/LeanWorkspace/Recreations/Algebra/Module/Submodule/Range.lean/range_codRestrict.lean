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

theorem range_codRestrict {τ₂₁ : R₂ →+* R} [RingHomSurjective τ₂₁] (p : Submodule R M)
    (f : M₂ →ₛₗ[τ₂₁] M) (hf) :
    LinearMap.range (codRestrict p f hf) = comap p.subtype (LinearMap.range f) := by
  simpa only [LinearMap.range_eq_map] using map_codRestrict _ _ _ _

