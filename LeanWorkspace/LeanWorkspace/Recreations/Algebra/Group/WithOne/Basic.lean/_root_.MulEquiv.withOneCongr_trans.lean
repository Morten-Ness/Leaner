import Mathlib

variable {α : Type u} {β : Type v} {γ : Type w}

variable [Mul α] [Mul β] [Mul γ]

theorem _root_.MulEquiv.withOneCongr_trans (e₁ : α ≃* β) (e₂ : β ≃* γ) :
    e₁.withOneCongr.trans e₂.withOneCongr = (e₁.trans e₂).withOneCongr := MulEquiv.toMonoidHom_injective (WithOne.mapMulHom_comp _ _).symm

