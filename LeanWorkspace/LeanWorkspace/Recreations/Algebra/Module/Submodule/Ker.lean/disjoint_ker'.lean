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

theorem disjoint_ker' {p : Submodule R M} :
    Disjoint p (LinearMap.ker f) ↔ ∀ x ∈ p, ∀ y ∈ p, f x = f y → x = y := by
  simp [LinearMap.disjoint_ker_iff_injOn, Set.InjOn]

