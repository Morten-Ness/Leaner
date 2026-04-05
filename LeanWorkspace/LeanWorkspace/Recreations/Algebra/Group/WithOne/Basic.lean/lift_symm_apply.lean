import Mathlib

variable {α : Type u} {β : Type v} {γ : Type w}

variable [Mul α] [MulOneClass β]

variable (f : α →ₙ* β)

theorem lift_symm_apply (f : WithOne α →* β) (x : α) : WithOne.lift.symm f x = f x := rfl

