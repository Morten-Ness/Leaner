import Mathlib

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}

variable {K : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable {V : Type*} {V₂ : Type*}

variable [Semiring R] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

variable {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}

variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]

theorem le_ker_iff_comp_subtype_eq_zero {N : Submodule R M} {f : M →ₛₗ[τ₁₂] M₂} :
    N ≤ LinearMap.ker f ↔ f ∘ₛₗ N.subtype = 0 := by
  rw [SetLike.le_def, LinearMap.ext_iff, Subtype.forall]; rfl

