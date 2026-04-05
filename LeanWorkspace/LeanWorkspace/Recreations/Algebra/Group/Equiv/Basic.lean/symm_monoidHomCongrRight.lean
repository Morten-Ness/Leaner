import Mathlib

variable {F α β M M₁ M₂ M₃ N N₁ N₂ N₃ P Q G H : Type*}

variable [EquivLike F α β]

variable [MulOneClass M] [MulOneClass M₁] [MulOneClass M₂] [MulOneClass M₃]
  [CommMonoid N] [CommMonoid N₁] [CommMonoid N₂] [CommMonoid N₃]

theorem symm_monoidHomCongrRight (e : N₁ ≃* N₂) :
    (MulEquiv.monoidHomCongrRight e).symm = MulEquiv.monoidHomCongrRight (M := M) e.symm := rfl

