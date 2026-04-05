import Mathlib

variable {α : Type u} {β : Type v} {γ : Type w}

variable [Mul α] [Mul β] [Mul γ]

theorem mapMulHom_mapMulHom (f : α →ₙ* β) (g : β →ₙ* γ) (x) :
    WithOne.mapMulHom g (WithOne.mapMulHom f x) = WithOne.mapMulHom (g.comp f) x := by
  induction x <;> rfl

