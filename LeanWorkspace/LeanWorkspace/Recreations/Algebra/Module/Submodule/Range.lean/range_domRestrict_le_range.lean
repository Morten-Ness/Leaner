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

theorem range_domRestrict_le_range [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) (S : Submodule R M) :
    LinearMap.range (f.domRestrict S) ≤ LinearMap.range f := by
  rintro x ⟨⟨y, hy⟩, rfl⟩
  exact LinearMap.mem_range_self f y

