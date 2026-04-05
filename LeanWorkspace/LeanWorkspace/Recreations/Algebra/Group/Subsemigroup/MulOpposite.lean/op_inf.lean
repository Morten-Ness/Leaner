import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem op_inf (S₁ S₂ : Subsemigroup M) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op := rfl

