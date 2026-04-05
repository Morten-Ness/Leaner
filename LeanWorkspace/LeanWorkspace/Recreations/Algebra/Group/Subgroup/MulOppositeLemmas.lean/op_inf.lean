import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem op_inf (S₁ S₂ : Subgroup G) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op := rfl

