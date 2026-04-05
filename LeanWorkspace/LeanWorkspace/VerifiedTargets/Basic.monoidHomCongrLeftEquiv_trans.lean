import Mathlib

variable {F α β M M₁ M₂ M₃ N N₁ N₂ N₃ P Q G H : Type*}

variable [EquivLike F α β]

variable [MulOneClass M] [MulOneClass M₁] [MulOneClass M₂] [MulOneClass M₃]
  [Monoid N] [Monoid N₁] [Monoid N₂] [Monoid N₃]

theorem monoidHomCongrLeftEquiv_trans (e₁₂ : M₁ ≃* M₂) (e₂₃ : M₂ ≃* M₃) :
    MulEquiv.monoidHomCongrLeftEquiv (N := N) (e₁₂.trans e₂₃) =
      (MulEquiv.monoidHomCongrLeftEquiv e₁₂).trans (MulEquiv.monoidHomCongrLeftEquiv e₂₃) := rfl

