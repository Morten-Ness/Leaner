import Mathlib

variable {α : Type u} {β : Type v} {γ : Type w}

variable [Mul α] [MulOneClass β]

variable (f : α →ₙ* β)

theorem lift_coe (x : α) : WithOne.lift f x = f x := rfl

