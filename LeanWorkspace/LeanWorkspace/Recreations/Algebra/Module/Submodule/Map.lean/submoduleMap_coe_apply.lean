import Mathlib

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₁] [Module R M] [Module R M₁]

theorem submoduleMap_coe_apply (f : M →ₗ[R] M₁) {p : Submodule R M} (x : p) :
    ↑(f.submoduleMap p x) = f x := rfl

