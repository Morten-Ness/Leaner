import Mathlib

variable {F α β M M₁ M₂ M₃ N N₁ N₂ N₃ P Q G H : Type*}

variable [EquivLike F α β]

variable [MulOneClass M] [MulOneClass M₁] [MulOneClass M₂] [MulOneClass M₃]
  [CommMonoid N] [CommMonoid N₁] [CommMonoid N₂] [CommMonoid N₃]

theorem monoidHomCongrLeft_trans (e₁₂ : M₁ ≃* M₂) (e₂₃ : M₂ ≃* M₃) :
    MulEquiv.monoidHomCongrLeft (N := N) (e₁₂.trans e₂₃) =
      (MulEquiv.monoidHomCongrLeft e₁₂).trans (MulEquiv.monoidHomCongrLeft e₂₃) := rfl

