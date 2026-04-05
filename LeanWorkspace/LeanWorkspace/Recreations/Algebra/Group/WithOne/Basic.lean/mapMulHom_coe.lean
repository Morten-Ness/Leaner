import Mathlib

variable {α : Type u} {β : Type v} {γ : Type w}

variable [Mul α] [Mul β] [Mul γ]

theorem mapMulHom_coe (f : α →ₙ* β) (a : α) : WithOne.mapMulHom f (a : WithOne α) = f a := rfl

