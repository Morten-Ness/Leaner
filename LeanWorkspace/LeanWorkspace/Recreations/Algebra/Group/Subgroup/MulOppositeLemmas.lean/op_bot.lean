import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem op_bot : (⊥ : Subgroup G).op = ⊥ := opEquiv.map_bot

