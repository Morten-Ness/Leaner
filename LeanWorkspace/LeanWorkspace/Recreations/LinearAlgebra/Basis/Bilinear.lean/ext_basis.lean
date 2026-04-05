import Mathlib

variable {ι₁ ι₂ : Type*}

variable {R R₂ S S₂ M N P Rₗ : Type*}

variable {Mₗ Nₗ Pₗ : Type*}

variable [Semiring R] [Semiring S] [Semiring R₂] [Semiring S₂] [CommSemiring Rₗ]

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]

variable [AddCommMonoid Mₗ] [AddCommMonoid Nₗ] [AddCommMonoid Pₗ]

variable [Module R M] [Module S N] [Module R₂ P] [Module S₂ P]

variable [Module Rₗ Mₗ] [Module Rₗ Nₗ] [Module Rₗ Pₗ]

variable [SMulCommClass S₂ R₂ P]

variable {ρ₁₂ : R →+* R₂} {σ₁₂ : S →+* S₂}

variable (b₁ : Basis ι₁ R M) (b₂ : Basis ι₂ S N) (b₁' : Basis ι₁ Rₗ Mₗ) (b₂' : Basis ι₂ Rₗ Nₗ)

theorem ext_basis {B B' : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P} (h : ∀ i j, B (b₁ i) (b₂ j) = B' (b₁ i) (b₂ j)) :
    B = B' := b₁.ext fun i => b₂.ext fun j => h i j

