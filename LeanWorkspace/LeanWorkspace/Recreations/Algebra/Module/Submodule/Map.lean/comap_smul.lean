import Mathlib

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable {K : Type*} {V : Type*} {V₂ : Type*}

variable [Semifield K]

variable [AddCommMonoid V] [Module K V]

variable [AddCommMonoid V₂] [Module K V₂]

theorem comap_smul (f : V →ₗ[K] V₂) (p : Submodule K V₂) (a : K) (h : a ≠ 0) :
    p.comap (a • f) = p.comap f := by
  ext b; simp only [Submodule.mem_comap, p.smul_mem_iff h, LinearMap.smul_apply]

