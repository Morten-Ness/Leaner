import Mathlib

variable {M α β : Type*} (e : α ≃ β)

theorem mulEquiv_symm_apply (e : α ≃ β) [Mul β] (b : β) :
    letI := Equiv.mul e
    (Equiv.mulEquiv e).symm b = e.symm b := rfl

