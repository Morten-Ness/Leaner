import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

theorem op_inf (S₁ S₂ : Subsemiring R) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op := rfl

