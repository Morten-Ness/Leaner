import Mathlib

variable {α : Type u} {β : Type v} {γ : Type w}

variable [Mul α] [Mul β] [Mul γ]

theorem mapMulHom_inj {f g : α →ₙ* β} : WithOne.mapMulHom f = WithOne.mapMulHom g ↔ f = g := WithOne.mapMulHom_injective'.eq_iff

