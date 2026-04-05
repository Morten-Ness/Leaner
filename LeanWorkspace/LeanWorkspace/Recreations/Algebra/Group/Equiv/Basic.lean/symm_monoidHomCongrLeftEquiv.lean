import Mathlib

variable {F α β M M₁ M₂ M₃ N N₁ N₂ N₃ P Q G H : Type*}

variable [EquivLike F α β]

variable [MulOneClass M] [MulOneClass M₁] [MulOneClass M₂] [MulOneClass M₃]
  [Monoid N] [Monoid N₁] [Monoid N₂] [Monoid N₃]

theorem symm_monoidHomCongrLeftEquiv (e : M₁ ≃* M₂) :
    (MulEquiv.monoidHomCongrLeftEquiv e).symm = MulEquiv.monoidHomCongrLeftEquiv (N := N) e.symm := rfl

