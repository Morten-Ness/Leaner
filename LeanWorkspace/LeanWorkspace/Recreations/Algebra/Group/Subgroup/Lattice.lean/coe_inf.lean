import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem coe_inf (p p' : Subgroup G) : ((p ⊓ p' : Subgroup G) : Set G) = (p : Set G) ∩ p' := rfl

