import Mathlib

variable {α : Type u} {β : Type v} {γ : Type w}

variable [Mul α] [Mul β] [Mul γ]

theorem mapMulHom_comp (f : α →ₙ* β) (g : β →ₙ* γ) :
    WithOne.mapMulHom (g.comp f) = (WithOne.mapMulHom g).comp (WithOne.mapMulHom f) := by
  ext x <;> cases x <;> rfl
