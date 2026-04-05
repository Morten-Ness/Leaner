import Mathlib

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable [Ring R] [AddCommGroup M] [Module R M] (p : Submodule R M)

variable [AddCommGroup M₂] [Module R M₂]

theorem map_toAddSubgroup (f : M →ₗ[R] M₂) (p : Submodule R M) :
    (p.map f).toAddSubgroup = p.toAddSubgroup.map (f : M →+ M₂) := rfl

