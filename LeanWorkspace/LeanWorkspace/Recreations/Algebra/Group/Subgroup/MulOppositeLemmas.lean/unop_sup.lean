import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem unop_sup (S₁ S₂ : Subgroup Gᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop := opEquiv.symm.map_sup _ _

