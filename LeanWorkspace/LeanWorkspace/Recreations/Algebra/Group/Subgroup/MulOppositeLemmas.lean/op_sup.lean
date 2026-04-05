import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem op_sup (S₁ S₂ : Subgroup G) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op := opEquiv.map_sup _ _

