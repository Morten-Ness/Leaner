import Mathlib

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable [Semiring R] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable (p p' : Submodule R M) (q q' : Submodule R₂ M₂)

variable {x : M}

theorem map_inf_eq_map_inf_comap [RingHomSurjective σ₁₂] {f : M →ₛₗ[σ₁₂] M₂} {p : Submodule R M}
    {p' : Submodule R₂ M₂} : Submodule.map f p ⊓ p' = Submodule.map f (p ⊓ Submodule.comap f p') := le_antisymm (by rintro _ ⟨⟨x, h₁, rfl⟩, h₂⟩; exact ⟨_, ⟨h₁, h₂⟩, rfl⟩)
    (le_inf (Submodule.map_mono inf_le_left) (Submodule.map_le_iff_le_comap.2 inf_le_right))

