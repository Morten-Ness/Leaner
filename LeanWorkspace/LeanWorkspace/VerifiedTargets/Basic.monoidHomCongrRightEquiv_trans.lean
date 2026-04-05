import Mathlib

variable {F α β M M₁ M₂ M₃ N N₁ N₂ N₃ P Q G H : Type*}

variable [EquivLike F α β]

variable [MulOneClass M] [MulOneClass M₁] [MulOneClass M₂] [MulOneClass M₃]
  [Monoid N] [Monoid N₁] [Monoid N₂] [Monoid N₃]

theorem monoidHomCongrRightEquiv_trans (e₁₂ : N₁ ≃* N₂) (e₂₃ : N₂ ≃* N₃) :
    MulEquiv.monoidHomCongrRightEquiv (M := M) (e₁₂.trans e₂₃) =
      (MulEquiv.monoidHomCongrRightEquiv e₁₂).trans (MulEquiv.monoidHomCongrRightEquiv e₂₃) := rfl

