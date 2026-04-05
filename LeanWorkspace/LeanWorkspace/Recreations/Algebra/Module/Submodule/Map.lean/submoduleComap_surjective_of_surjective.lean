import Mathlib

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₁] [Module R M] [Module R M₁]

theorem submoduleComap_surjective_of_surjective (f : M →ₗ[R] M₁) (q : Submodule R M₁)
    (hf : Function.Surjective f) : Function.Surjective (f.submoduleComap q) := fun y ↦ by
  obtain ⟨x, hx⟩ := hf y
  use ⟨x, Submodule.mem_comap.mpr (hx ▸ y.2)⟩
  apply Subtype.val_injective
  simp [hx]

