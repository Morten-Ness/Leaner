import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Group M] [Group N] [Group P] {f : M →* N} {g : N →* P}

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Type*} [CommMonoid X₁] [CommMonoid X₂] [CommMonoid X₃]
  [CommMonoid Y₁] [CommMonoid Y₂] [CommMonoid Y₃]
  (e₁ : X₁ ≃* Y₁) (e₂ : X₂ ≃* Y₂) (e₃ : X₃ ≃* Y₃)
  {f₁₂ : X₁ →* X₂} {f₂₃ : X₂ →* X₃} {g₁₂ : Y₁ →* Y₂} {g₂₃ : Y₂ →* Y₃}

theorem iff_of_ladder_mulEquiv (comm₁₂ : g₁₂.comp e₁ = MonoidHom.comp e₂ f₁₂)
    (comm₂₃ : g₂₃.comp e₂ = MonoidHom.comp e₃ f₂₃) : Function.MulExact g₁₂ g₂₃ ↔ Function.MulExact f₁₂ f₂₃ := (MonoidHom.mulExact_iff_of_surjective_of_bijective_of_injective _ _ _ _ e₁ e₂ e₃ comm₁₂ comm₂₃
    e₁.surjective e₂.bijective e₃.injective).symm

