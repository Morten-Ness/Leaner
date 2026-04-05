import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem bot_toSubmonoid : (⊥ : Subgroup G).toSubmonoid = ⊥ := rfl

