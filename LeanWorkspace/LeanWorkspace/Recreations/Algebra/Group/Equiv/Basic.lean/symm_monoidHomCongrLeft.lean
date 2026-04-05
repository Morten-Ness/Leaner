import Mathlib

variable {F α β M M₁ M₂ M₃ N N₁ N₂ N₃ P Q G H : Type*}

variable [EquivLike F α β]

variable [MulOneClass M] [MulOneClass M₁] [MulOneClass M₂] [MulOneClass M₃]
  [CommMonoid N] [CommMonoid N₁] [CommMonoid N₂] [CommMonoid N₃]

theorem symm_monoidHomCongrLeft (e : M₁ ≃* M₂) :
    (MulEquiv.monoidHomCongrLeft e).symm = MulEquiv.monoidHomCongrLeft (N := N) e.symm := rfl

