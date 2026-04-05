import Mathlib

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₁] [Module R M] [Module R M₁]

variable [Semiring R₂] [AddCommMonoid M₂] [Module R₂ M₂] {σ₂₁ : R₂ →+* R}

theorem map_codRestrict [RingHomSurjective σ₂₁] (p : Submodule R M) (f : M₂ →ₛₗ[σ₂₁] M) (h p') :
    Submodule.map (codRestrict p f h) p' = Submodule.comap p.subtype (p'.map f) := Submodule.ext fun ⟨x, hx⟩ => by simp [Subtype.ext_iff]

