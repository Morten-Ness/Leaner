import Mathlib

variable {R R₁ R₂ R₃ R₄ S M M₁ M₂ M₃ M₄ N₁ N₂ : Type*}

variable [Semiring R] [Semiring S]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]

variable {modM : Module R M} {modM₂ : Module S M₂} {σ : R →+* S} {σ' : S →+* R}

variable [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

theorem toLinearMap_injective : Function.Injective (toLinearMap : (M ≃ₛₗ[σ] M₂) → M →ₛₗ[σ] M₂) := fun _ _ H ↦ LinearEquiv.toEquiv_injective <| Equiv.ext <| LinearMap.congr_fun H

