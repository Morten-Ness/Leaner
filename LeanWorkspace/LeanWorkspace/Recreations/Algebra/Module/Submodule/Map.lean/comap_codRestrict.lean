import Mathlib

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₁] [Module R M] [Module R M₁]

variable [Semiring R₂] [AddCommMonoid M₂] [Module R₂ M₂] {σ₂₁ : R₂ →+* R}

theorem comap_codRestrict (p : Submodule R M) (f : M₂ →ₛₗ[σ₂₁] M) (hf p') :
    Submodule.comap (codRestrict p f hf) p' = Submodule.comap f (Submodule.map p.subtype p') := Submodule.ext fun x => ⟨fun h => ⟨⟨_, hf x⟩, h, rfl⟩, by rintro ⟨⟨_, _⟩, h, ⟨⟩⟩; exact h⟩

