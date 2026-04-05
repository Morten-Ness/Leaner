import Mathlib

variable {α : Type u} {β : Type v} {γ : Type w}

variable [Mul α] [MulOneClass β]

variable (f : α →ₙ* β)

theorem lift_unique (f : WithOne α →* β) : f = WithOne.lift (f.toMulHom.comp WithOne.coeMulHom) := (WithOne.lift.apply_symm_apply f).symm

