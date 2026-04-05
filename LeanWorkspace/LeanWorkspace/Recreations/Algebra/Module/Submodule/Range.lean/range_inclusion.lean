import Mathlib

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}

variable {K : Type*}

variable {M : Type*} {M₂ : Type*} {M₃ : Type*}

variable {V : Type*} {V₂ : Type*}

variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]

variable [Module R M] [Module R₂ M₂]

variable (p : Submodule R M)

variable {τ₁₂ : R →+* R₂}

theorem range_inclusion (p q : Submodule R M) (h : p ≤ q) :
    LinearMap.range (inclusion h) = comap q.subtype p := by
  rw [← Submodule.map_top, inclusion, LinearMap.map_codRestrict, Submodule.map_top, Submodule.range_subtype]

