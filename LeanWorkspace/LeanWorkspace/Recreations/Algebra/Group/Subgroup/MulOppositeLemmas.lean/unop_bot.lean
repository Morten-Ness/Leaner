import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem unop_bot : (⊥ : Subgroup Gᵐᵒᵖ).unop = ⊥ := opEquiv.symm.map_bot

