import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem coe_bot : ((⊥ : Subgroup G) : Set G) = {1} := rfl

