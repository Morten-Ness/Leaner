import Mathlib

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}

variable {K : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable {V : Type*} {V₂ : Type*}

variable [Semifield K]

variable [AddCommMonoid V] [Module K V]

variable [AddCommMonoid V₂] [Module K V₂]

theorem ker_smul' (f : V →ₗ[K] V₂) (a : K) : LinearMap.ker (a • f) = ⨅ _ : a ≠ 0, LinearMap.ker f := Submodule.comap_smul' f _ a

