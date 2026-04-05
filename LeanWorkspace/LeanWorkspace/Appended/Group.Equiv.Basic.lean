import Mathlib

section

variable {F α β M M₁ M₂ M₃ N N₁ N₂ N₃ P Q G H : Type*}

variable [EquivLike F α β]

variable [MulOneClass M] [MulOneClass M₁] [MulOneClass M₂] [MulOneClass M₃]
  [Monoid N] [Monoid N₁] [Monoid N₂] [Monoid N₃]

theorem monoidHomCongrLeftEquiv_trans (e₁₂ : M₁ ≃* M₂) (e₂₃ : M₂ ≃* M₃) :
    MulEquiv.monoidHomCongrLeftEquiv (N := N) (e₁₂.trans e₂₃) =
      (MulEquiv.monoidHomCongrLeftEquiv e₁₂).trans (MulEquiv.monoidHomCongrLeftEquiv e₂₃) := rfl

end

section

variable {F α β M M₁ M₂ M₃ N N₁ N₂ N₃ P Q G H : Type*}

variable [EquivLike F α β]

variable [MulOneClass M] [MulOneClass M₁] [MulOneClass M₂] [MulOneClass M₃]
  [CommMonoid N] [CommMonoid N₁] [CommMonoid N₂] [CommMonoid N₃]

theorem monoidHomCongrLeft_trans (e₁₂ : M₁ ≃* M₂) (e₂₃ : M₂ ≃* M₃) :
    MulEquiv.monoidHomCongrLeft (N := N) (e₁₂.trans e₂₃) =
      (MulEquiv.monoidHomCongrLeft e₁₂).trans (MulEquiv.monoidHomCongrLeft e₂₃) := rfl

end

section

variable {F α β M M₁ M₂ M₃ N N₁ N₂ N₃ P Q G H : Type*}

variable [EquivLike F α β]

variable [MulOneClass M] [MulOneClass M₁] [MulOneClass M₂] [MulOneClass M₃]
  [Monoid N] [Monoid N₁] [Monoid N₂] [Monoid N₃]

theorem monoidHomCongrRightEquiv_trans (e₁₂ : N₁ ≃* N₂) (e₂₃ : N₂ ≃* N₃) :
    MulEquiv.monoidHomCongrRightEquiv (M := M) (e₁₂.trans e₂₃) =
      (MulEquiv.monoidHomCongrRightEquiv e₁₂).trans (MulEquiv.monoidHomCongrRightEquiv e₂₃) := rfl

end

section

variable {F α β M M₁ M₂ M₃ N N₁ N₂ N₃ P Q G H : Type*}

variable [EquivLike F α β]

variable [MulOneClass M] [MulOneClass M₁] [MulOneClass M₂] [MulOneClass M₃]
  [CommMonoid N] [CommMonoid N₁] [CommMonoid N₂] [CommMonoid N₃]

theorem monoidHomCongrRight_trans (e₁₂ : N₁ ≃* N₂) (e₂₃ : N₂ ≃* N₃) :
    MulEquiv.monoidHomCongrRight (M := M) (e₁₂.trans e₂₃) =
      (MulEquiv.monoidHomCongrRight e₁₂).trans (MulEquiv.monoidHomCongrRight e₂₃) := rfl

end
