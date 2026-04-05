import Mathlib

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}

variable {K : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable {V : Type*} {V₂ : Type*}

variable [Ring R] [Ring R₂]

variable [AddCommGroup M] [AddCommGroup M₂]

variable [Module R M] [Module R₂ M₂]

variable {τ₁₂ : R →+* R₂}

variable {f : M →ₛₗ[τ₁₂] M₂}

theorem disjoint_ker_iff_injOn {p : Submodule R M} :
    Disjoint p (LinearMap.ker f) ↔ Set.InjOn f p := by
  rw [LinearMap.disjoint_ker, Set.injOn_iff_map_eq_zero]

