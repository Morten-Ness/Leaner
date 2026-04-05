import Mathlib

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}

variable {K : Type*}

variable {M : Type*} {M₂ : Type*} {M₃ : Type*}

variable {V : Type*} {V₂ : Type*}

variable [Semiring R] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

variable {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}

variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]

theorem _root_.Submodule.map_comap_eq [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂)
    (q : Submodule R₂ M₂) :
    map f (comap f q) = LinearMap.range f ⊓ q := le_antisymm (le_inf LinearMap.map_le_range (map_comap_le _ _)) <| by
    rintro _ ⟨⟨x, _, rfl⟩, hx⟩; exact ⟨x, hx, rfl⟩

