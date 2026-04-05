import Mathlib

variable {M α β : Type*} (e : α ≃ β)

theorem mulEquiv_apply (e : α ≃ β) [Mul β] (a : α) : (Equiv.mulEquiv e) a = e a := rfl

