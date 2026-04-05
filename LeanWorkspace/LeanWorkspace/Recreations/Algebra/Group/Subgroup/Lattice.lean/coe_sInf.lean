import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem coe_sInf (H : Set (Subgroup G)) : ((sInf H : Subgroup G) : Set G) = ⋂ s ∈ H, ↑s := rfl

