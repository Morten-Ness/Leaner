import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem op_inf (S₁ S₂ : Submonoid M) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op := rfl

