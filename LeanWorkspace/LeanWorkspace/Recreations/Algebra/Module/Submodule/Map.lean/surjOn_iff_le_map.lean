import Mathlib

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable [Semiring R] [Semiring R₂]

variable [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂]

variable {τ₁₂ : R →+* R₂} {τ₂₁ : R₂ →+* R}

variable [RingHomInvPair τ₁₂ τ₂₁] [RingHomInvPair τ₂₁ τ₁₂]

variable (p : Submodule R M) (q : Submodule R₂ M₂)

theorem surjOn_iff_le_map [RingHomSurjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂} {p : Submodule R M}
    {q : Submodule R₂ M₂} : Set.SurjOn f p q ↔ q ≤ p.map f := Iff.rfl

