import Mathlib

variable {α β : Type*} (e : α ≃ β)

theorem ringEquiv_apply (e : α ≃ β) [Add β] [Mul β] (a : α) : Equiv.ringEquiv e a = e a := rfl

