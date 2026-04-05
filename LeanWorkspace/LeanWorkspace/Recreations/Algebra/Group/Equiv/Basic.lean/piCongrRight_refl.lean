import Mathlib

variable {F α β M M₁ M₂ M₃ N N₁ N₂ N₃ P Q G H : Type*}

variable [EquivLike F α β]

theorem piCongrRight_refl {η : Type*} {Ms : η → Type*} [∀ j, Mul (Ms j)] :
    (MulEquiv.piCongrRight fun j => MulEquiv.refl (Ms j)) = MulEquiv.refl _ := rfl

