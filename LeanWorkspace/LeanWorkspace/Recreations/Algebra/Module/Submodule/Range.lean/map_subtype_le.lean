import Mathlib

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}

variable {K : Type*}

variable {M : Type*} {M₂ : Type*} {M₃ : Type*}

variable {V : Type*} {V₂ : Type*}

variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]

variable [Module R M] [Module R₂ M₂]

variable (p : Submodule R M)

variable {τ₁₂ : R →+* R₂}

theorem map_subtype_le (p' : Submodule R p) : map p.subtype p' ≤ p := by
  simpa using (LinearMap.map_le_range : map p.subtype p' ≤ LinearMap.range p.subtype)

