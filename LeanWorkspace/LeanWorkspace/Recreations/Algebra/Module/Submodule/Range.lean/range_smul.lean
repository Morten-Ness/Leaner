import Mathlib

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}

variable {K : Type*}

variable {M : Type*} {M₂ : Type*} {M₃ : Type*}

variable {V : Type*} {V₂ : Type*}

variable [Semifield K]

variable [AddCommMonoid V] [Module K V]

variable [AddCommMonoid V₂] [Module K V₂]

theorem range_smul (f : V →ₗ[K] V₂) (a : K) (h : a ≠ 0) : LinearMap.range (a • f) = LinearMap.range f := by
  simpa only [LinearMap.range_eq_map] using Submodule.map_smul f _ a h

