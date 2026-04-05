import Mathlib

variable {α : Type u} {β : Type v} {γ : Type w}

variable [Mul α] [MulOneClass β]

variable (f : α →ₙ* β)

theorem lift_one : WithOne.lift f 1 = 1 := rfl

