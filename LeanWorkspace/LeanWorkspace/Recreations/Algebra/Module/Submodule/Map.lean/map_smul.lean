import Mathlib

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable {K : Type*} {V : Type*} {V₂ : Type*}

variable [Semifield K]

variable [AddCommMonoid V] [Module K V]

variable [AddCommMonoid V₂] [Module K V₂]

theorem map_smul (f : V →ₗ[K] V₂) (p : Submodule K V) (a : K) (h : a ≠ 0) :
    p.map (a • f) = p.map f := le_antisymm (by rw [Submodule.map_le_iff_le_comap, Submodule.comap_smul f _ a h, ← Submodule.map_le_iff_le_comap])
    (by rw [Submodule.map_le_iff_le_comap, ← Submodule.comap_smul f _ a h, ← Submodule.map_le_iff_le_comap])

