import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

theorem op_inf (S₁ S₂ : Subring R) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op := rfl

