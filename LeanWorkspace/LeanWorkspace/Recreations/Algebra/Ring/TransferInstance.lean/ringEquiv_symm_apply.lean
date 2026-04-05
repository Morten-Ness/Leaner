import Mathlib

variable {α β : Type*} (e : α ≃ β)

theorem ringEquiv_symm_apply (e : α ≃ β) [Add β] [Mul β] (b : β) : by
    letI := Equiv.add e
    letI := Equiv.mul e
    exact (Equiv.ringEquiv e).symm b = e.symm b := rfl

