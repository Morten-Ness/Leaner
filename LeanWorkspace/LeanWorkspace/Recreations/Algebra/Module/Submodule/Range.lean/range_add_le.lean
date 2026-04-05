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

theorem range_add_le [RingHomSurjective τ₁₂] (f g : M →ₛₗ[τ₁₂] M₂) :
    LinearMap.range (f + g) ≤ LinearMap.range f ⊔ LinearMap.range g := by
  rintro - ⟨_, rfl⟩
  apply add_mem_sup
  all_goals simp only [LinearMap.mem_range, exists_apply_eq_apply]

