import Mathlib

variable {R R₁ R₂ R₃ R₄ S M M₁ M₂ M₃ M₄ N₁ N₂ : Type*}

variable [Semiring R] [Semiring S]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]

variable {modM : Module R M} {modM₂ : Module S M₂} {σ : R →+* S} {σ' : S →+* R}

variable [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

theorem toEquiv_injective :
    (LinearEquiv.toEquiv (modM := modM) (modM₂ := modM₂) : (M ≃ₛₗ[σ] M₂) → M ≃ M₂).Injective :=
  fun ⟨⟨⟨_, _⟩, _⟩, _, _, _⟩ ⟨⟨⟨_, _⟩, _⟩, _, _, _⟩ h ↦
    (LinearEquiv.mk.injEq _ _ _ _ _ _ _ _).mpr
      ⟨LinearMap.ext (congr_fun (Equiv.mk.inj h).1), (Equiv.mk.inj h).2⟩

